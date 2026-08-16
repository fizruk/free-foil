{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
-- | The MLTT interpreter: the generated syntax, the evaluator, the type checker
-- and the resolver glued into a program that reads modules.
--
-- A module is introduced by a @module@ header and runs to the next one. Usually
-- a file holds one, and the interpreter takes any number of files; but nothing
-- stops a file from holding several, which is what the tests and
-- @examples/modules.mltt@ do so that a whole example fits in one place. Build
-- order is computed over every module the interpreter was given, wherever it
-- came from.
--
-- > module Data.Nat
-- > import Prelude
-- >
-- > namespace Nat where
-- >   def id : Π (A : 𝕌) → A → A := λ A ⇒ λ x ⇒ x
-- >   private def helper : 𝟙 := tt
-- >
-- > open Nat
-- > compute id 𝟙 tt
--
-- Everything lives in one growing foil scope: a top-level definition is an
-- ordinary 'Foil.Name' whose 'Def' says what it unfolds to, and a module,
-- namespace or @import@ decides only /which spellings can reach which name/.
-- That split is what makes @private@ cheap, and it is worth stating plainly:
--
-- * 'envDeclared' is a name table, so making a helper private removes a
--   spelling and nothing else;
-- * 'ctxDefs' is untouched by any of it, so conversion still unfolds that
--   helper wherever it already occurs in a checked term.
--
-- A client therefore cannot /name/ a private helper but can still /reduce/
-- through it, which is the behaviour a proof assistant needs and the reason
-- narrowing belongs above the library rather than inside it.
module Language.MLTT.Impl where

import           Control.DeepSeq              (NFData)
import           Control.Monad                (foldM)
import qualified Control.Monad.Foil           as Foil
import qualified Control.Monad.Foil.Blocks    as Blocks
import           Control.Monad.Foil.Registry  (StripeIndex (..))
import qualified Control.Monad.Foil.Registry  as Registry
import           Data.Functor.Compose         (Compose (..))
import           Data.Functor.Identity        (Identity (..))
import           Control.Monad.Free.Foil      (AST (Var), UnresolvedName (..))
import           Data.List                    (foldl', group, intercalate, sort)
import           Data.Map                     (Map)
import           Data.String                  (IsString)
import           Data.Maybe                   (listToMaybe)
import qualified Data.Map                     as Map
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Language.MLTT.Eval
import           Language.MLTT.FreeFoilConfig (intToVarIdent)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Telescope
import           Language.MLTT.Typecheck

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import Language.MLTT.Impl.Generated (sourceLines)

-- * The elaboration environment

-- | What each name in scope is called: the read-back direction of a 'Table'.
--
-- This is a 'Foil.NameMap', and it is /total/ on the top-level scope, because
-- the only thing that extends that scope is a definition and every definition
-- is entered here. Bound variables never reach it: 'showTermWith' sends a name
-- back through the binders it passed and only consults the map for what is
-- free in the whole term.
--
-- It is also the seed of the interner a serialisation layer would need, since
-- a 'Foil.Name' is an allocation artefact and cannot be written to disk.
type Display = Foil.NameMap

-- | Everything carried from one declaration to the next.
data Env n = Env
  { envCtx      :: Ctx Raw.BNFC'Position n
    -- ^ Scope, types and definitions: the foil half.
  , envDeclared :: Table (Foil.Name n)
    -- ^ Fully qualified names reachable in the module being checked, including
    -- what its imports brought in.
  , envExports  :: Table (Foil.Name n)
    -- ^ Those declarations of the current module that are public.
  , envModules  :: Map Raw.VarIdent (Table (Foil.Name n))
    -- ^ What each module checked so far exports.
  , envDisplay  :: Display n Raw.VarIdent
    -- ^ What each top-level name is called.
  , envManifest :: Table (Term n)
    -- ^ Spellings that stand for a /term/ rather than a name: the manifest
    -- fields of the module's parameter block. A manifest field is an
    -- abbreviation, so it is never a variable, never discharged over, and
    -- resolved by putting its value in place. Emptied at a module boundary,
    -- since a parameter block belongs to one module.
  , envClosedOver :: Table ([Raw.VarIdent], Foil.Name n)
    -- ^ For each declaration of the module being checked, the parameters it
    -- was closed over and its name. A reference to one of them from inside the
    -- same module is put back together with those parameters; see
    -- 'splitVisible'. It is emptied at a module boundary, since a client sees
    -- the closed constant and applies it itself.
    --
    -- The declaration's own 'Foil.Name' is recorded here, rather than looked up
    -- by spelling later, because a module parameter may shadow the spelling.
    -- It sits second in the pair so that the pair is a 'Functor' over it, and
    -- the whole table sinks as a coercion (see 'extendEnv').
  }

-- | An empty environment, before any module is checked.
emptyEnv :: Env Foil.VoidS
emptyEnv = Env emptyCtx Map.empty Map.empty Map.empty Foil.emptyNameMap Map.empty Map.empty

-- | Extend an environment with one top-level definition.
--
-- Every map is a container of sinkables, so widening them is a coercion, and
-- only the new entry is inserted. The nested containers (the tables of the
-- module map, the pairs of 'envClosedOver') are sunk through 'Compose', the
-- same idiom 'Foil.sink1' itself uses one level down, so no spine is
-- walked anywhere.
extendEnv
  :: Foil.DExt n l
  => Ctx Raw.BNFC'Position l
  -> Foil.NameBinder n l
  -> Raw.VarIdent           -- ^ The fully qualified name of the definition.
  -> Visibility             -- ^ Does it leave the module?
  -> Env n
  -> Env l
extendEnv ctx binder full visibility env = Env
  { envCtx      = ctx
  , envDeclared = Map.insert full name (Foil.sink1 (envDeclared env))
  , envExports  = export visibility full name (Foil.sink1 (envExports env))
  , envModules  = getCompose (Foil.sink1 (Compose (envModules env)))
  , envDisplay  = Foil.addNameBinder binder full (envDisplay env)
  , envManifest = Foil.sink1 (envManifest env)
  , envClosedOver = getCompose (Foil.sink1 (Compose (envClosedOver env)))
  }
  where
    name = Foil.nameOf binder

-- | Print a term, showing top-level definitions by name and bound variables by
-- their index.
display :: Foil.Distinct n => Env n -> Term n -> RenderedTerm
display env = RenderedTerm . showTermWith intToVarIdent (envDisplay env)

-- * Results

-- | A name as shown to the user: a fully qualified spelling, not a
-- 'Foil.Name'. Distinct from 'RenderedTerm' so that the two cannot be mixed
-- up in a 'CommandResult'.
newtype RenderedName = RenderedName { renderedName :: String }
  deriving newtype (Eq, Show, IsString, NFData)

-- | A term as shown to the user, printed by 'display'. Distinct from
-- 'StoredTerm' in "Language.MLTT.Artifact", which keeps the term's bytes
-- for loading rather than prose for the user.
newtype RenderedTerm = RenderedTerm { renderedTerm :: String }
  deriving newtype (Eq, Show, IsString, NFData)

-- | The prose of a failure, whatever layer it came from: a 'ParseError', a
-- 'TypeError', a 'LinkError' — by the time it reaches a result, it is only
-- shown.
type ErrorMessage = String

-- | Render a fully qualified name the way results show it.
renderVarIdent :: Raw.VarIdent -> RenderedName
renderVarIdent = RenderedName . prettyVarIdent

-- | What interpreting one declaration produced.
data CommandResult
  = EnteredModule RenderedName  -- ^ A module was reached in build order.
  | LoadedModule RenderedName   -- ^ A module was loaded from its cached
                                -- artifact; its @check@ and @compute@
                                -- commands are not re-run.
  | Defined RenderedName [RenderedName]
                                -- ^ @def@ succeeded, for the fully qualified
                                -- name and the module parameters it was
                                -- discharged over.
  | Checked RenderedTerm RenderedTerm
                                -- ^ @check@ succeeded, for a term and its type.
  | Computed RenderedTerm       -- ^ @compute@ succeeded, with the normal form.
  | Imported RenderedName       -- ^ An interactive @import@ brought a
                                -- module's exports into the session.
  | Failed ErrorMessage         -- ^ The declaration was rejected.
  deriving (Eq, Generic, Show)

-- | Forcing a result forces the checking that produced it; the parallel
-- builder relies on this to keep each module's work on its own thread.
instance NFData CommandResult

-- | Did everything succeed?
succeeded :: [CommandResult] -> Bool
succeeded = all $ \case
  Failed _ -> False
  _        -> True

-- | Render a result the way the executable prints it.
renderResult :: CommandResult -> String
renderResult = \case
  EnteredModule name -> "module " <> renderedName name
  LoadedModule name  -> "module " <> renderedName name <> " (cached)"
  Defined name []    -> "  ✓ defined " <> renderedName name
  Defined name used  -> "  ✓ defined " <> renderedName name
                          <> " over (" <> intercalate ", " (map renderedName used) <> ")"
  Checked term ty    -> "  ✓ " <> renderedTerm term <> " : " <> renderedTerm ty
  Computed term      -> "  ↦ " <> renderedTerm term
  Imported name      -> "  ✓ imported " <> renderedName name
  Failed err         -> "  ✗ " <> err

-- * Build order

-- | What ordering or linking a set of modules can report: a missing or
-- cyclic import, or overlapping reservations.
type BuildError = String

-- | Order the modules so that every module comes after the ones it imports.
--
-- Reports an import of a module that is not present, and an import cycle,
-- rather than looping or crashing.
buildOrder :: [Raw.Module] -> Either BuildError [Raw.Module]
buildOrder modules
  | not (null missing) = Left ("imported module not found: " <> intercalate ", " missing)
  | otherwise = reverse <$> foldM (visit Set.empty) [] (map moduleName modules)
  where
    byName = Map.fromList [(moduleName m, m) | m <- modules]
    importsOf m = [x | Raw.AnImport _ x <- moduleImports m]
    missing =
      [ x | m <- modules, Raw.VarIdent x <- importsOf m
      , Raw.VarIdent x `Map.notMember` byName ]

    visit onPath done name
      | name `Set.member` onPath =
          Left ("import cycle through module " <> prettyVarIdent name)
      | any ((== name) . moduleName) done = Right done
      | otherwise = case Map.lookup name byName of
          Nothing -> Right done   -- already reported above
          Just m -> do
            done' <- foldM (visit (Set.insert name onPath)) done (importsOf m)
            return (m : done')

-- | The name of a module.
moduleName :: Raw.Module -> Raw.VarIdent
moduleName (Raw.AModule _ name _ _ _ _) = name

-- | The parameters of a module.
--
-- Note that this is the block after 'resolveUnits' has put the included fields
-- in front of it, since that is the only shape a module reaches the checker in.
moduleParams :: Raw.Module -> [Raw.Param]
moduleParams (Raw.AModule _ _ _ params _ _) = params

-- | The imports of a module.
moduleImports :: Raw.Module -> [Raw.Import]
moduleImports (Raw.AModule _ _ _ _ imports _) = imports

-- | The declarations of a module.
moduleDecls :: Raw.Module -> [Raw.Decl]
moduleDecls (Raw.AModule _ _ _ _ _ decls) = decls

-- * Telescopes and includes

-- | The telescopes a program declares, by name.
type Telescopes = Map Raw.VarIdent [Raw.Param]

-- | Split a program's units and resolve every @include@ clause.
--
-- An include is expanded into the module's parameter block, so that nothing
-- downstream has to know about telescopes: what comes out is an ordinary
-- parametrised module, elaborated and discharged as before. Expanding before
-- the module is hashed is also what makes an include behave like an import for
-- staleness, since a changed telescope changes the printed form of every module
-- that includes it.
--
-- The included fields come first, in the order the clauses are written, and the
-- module's own parameters follow. A telescope may be included by any number of
-- modules and is elaborated afresh in each, which is what keeps the elaboration
-- canonical: nothing is shared between two modules but the source.
--
-- A telescope may itself include telescopes, so a theory can extend a poorer
-- theory: @telescope Monoid include Semigroup (unit : A) …@ is the monoid
-- block built on the semigroup one. Telescope includes are expanded first, in
-- dependency order over the declared telescopes with a cycle reported by name
-- — the same shape as the build order over modules — so by the time a module
-- includes a telescope, the telescope is a plain parameter list. A refined
-- include composes unchanged, since refining a parameter list yields a
-- parameter list.
resolveUnits :: [Raw.Unit] -> Either BuildError [Raw.Module]
resolveUnits units
  | (dup : _) <- duplicates = Left ("telescope declared twice: " <> prettyVarIdent dup)
  | otherwise = do
      telescopes <- foldM expandDeclared Map.empty (Map.keys rawTelescopes)
      traverse (expandIncludes telescopes) modules
  where
    declared = [t | Raw.UnitTelescope _ t <- units]
    modules  = [m | Raw.UnitModule _ m <- units]

    rawTelescopes :: Map Raw.VarIdent ([Raw.Include], [Raw.Param])
    rawTelescopes = Map.fromList
      [(name, (incs, params)) | Raw.ATelescope _ name incs params <- declared]

    duplicates =
      [name | name : _ : _ <- group (sort [name | Raw.ATelescope _ name _ _ <- declared])]

    -- Expand one declared telescope into the memo, dependencies first. The
    -- path carries the includes being expanded, outermost last, so a cycle is
    -- reported in the order it is entered.
    expandDeclared done name = fst <$> expandTelescope [] done name

    expandTelescope path done name
      | name `elem` path =
          Left ("telescopes include each other in a cycle: "
                 <> intercalate " -> "
                      (map prettyVarIdent (reverse (name : path))))
      | Just params <- Map.lookup name done = Right (done, params)
      | Just (incs, params) <- Map.lookup name rawTelescopes = do
          (done', included) <- foldM (includeInto (name : path)) (done, []) incs
          let expanded = included <> params
          return (Map.insert name expanded done', expanded)
      | otherwise =
          Left ("no telescope named " <> prettyVarIdent name <> " is declared")

    includeInto path (done, acc) (Raw.AnInclude _loc name refinement) = do
      (done', params) <- expandTelescope path done name
      fixed <- refinementOf name params refinement
      return (done', acc <> map (fixParam fixed) params)

    expandIncludes telescopes (Raw.AModule loc name includes params imports decls) = do
      included <- concat <$> traverse (include telescopes) includes
      return (Raw.AModule loc name [] (included <> params) imports decls)

    include telescopes (Raw.AnInclude _loc name refinement) =
      case Map.lookup name telescopes of
        Nothing -> Left ("no telescope named " <> prettyVarIdent name <> " is declared")
        Just params -> do
          fixed <- refinementOf name params refinement
          return (map (fixParam fixed) params)

    -- A refined field keeps its place in the telescope and becomes manifest,
    -- so the residual is the same block with fewer variables in it.
    fixParam fixed param@(Raw.AParam loc field ty) = case Map.lookup field fixed of
      -- The field keeps its declared type, so the supplied value is checked
      -- against it exactly as the field would have been used.
      Just value -> Raw.AManifest loc field ty value
      Nothing    -> param
    fixParam _ param@Raw.AManifest{} = param

    refinementOf _name _params (Raw.NoRefinement _loc) = Right Map.empty
    refinementOf name params (Raw.ARefinement _loc fixes)
      | (dup : _) <- repeated =
          Left ("field fixed twice: " <> prettyVarIdent dup)
      | (already : _) <- [x | x <- fixedNames, x `elem` manifest] =
          Left ("field " <> prettyVarIdent already <> " of telescope "
                 <> prettyVarIdent name <> " is already fixed")
      | (unknown : _) <- [x | x <- fixedNames, x `notElem` bound] =
          Left ("telescope " <> prettyVarIdent name <> " has no field "
                 <> prettyVarIdent unknown)
      | otherwise = Right (Map.fromList [(x, value) | Raw.AFixed _ x value <- fixes])
      where
        fixedNames = [x | Raw.AFixed _ x _ <- fixes]
        repeated   = [x | x : _ : _ <- group (sort fixedNames)]
        bound      = [x | Raw.AParam _ x _ <- params]
        manifest   = [x | Raw.AManifest _ x _ _ <- params]

-- * Name layout
--
-- $namelayout
-- The allocators never cross zero. Module declarations, the interned
-- constants, live in stripes /below/ zero; everything term-internal lives
-- at or above it; and a constant is recognised by its sign. Thus the two
-- halves can never collide, by construction, which is what the wire
-- format's verbatim locals and the linker's disjointness both rest on.
-- On the other side, free-foil's successor allocator is guarded to never
-- dip below zero, so a transient name minted against a scope of constants
-- stays out of their region.

-- | How many top-level names a module may declare.
stripeSize :: Registry.StripeSize
stripeSize = Registry.StripeSize 0x100000

-- | The region module parameters and elaboration-time binders live in: every
-- non-negative name, now that the stripes lie below zero.
--
-- Nothing here can collide with a declaration's name, and the indices stay
-- small: a discharged type prints as @Π (x0 : 𝕌) → …@ however many
-- declarations precede it. More importantly, allocation inside the region
-- depends only on the region's own content, so elaborating a declaration
-- produces the same term whatever else the ambient scope holds. Thus
-- elaborated terms, and hence artifacts and their hashes, are canonical
-- across worlds.
--
-- What lands here is one name per binder /written/ in the declaration being
-- elaborated, plus the parameters, and the region resets between
-- declarations, since elaboration binders live inside terms and never enter
-- the module's scope. Evaluation and type checking also mint their
-- transient names here (the guarded successor allocates at the region's
-- occupied top), and nothing rests on those.
localRegion :: Foil.NameRange
localRegion = Foil.NameRange 0 maxBound

-- | The demo's stripe layout: runs of 'stripeSize' names below zero,
-- descending, per "Control.Monad.Foil.Registry". The registry machinery
-- itself lives in the library now; what stays here is this policy.
mlttStripes :: Registry.StripeLayout
mlttStripes = Registry.stripesBelowZero stripeSize

-- | Which stripe each module's declarations live in; see
-- "Control.Monad.Foil.Registry" for why the assignment is persistent and
-- append-only. Here it is threaded through one run, and a test (or a driver)
-- can seed it.
type Registry = Registry.Registry Raw.VarIdent

-- | The registry before any module has ever been checked.
emptyRegistry :: Registry
emptyRegistry = Registry.emptyRegistry

-- | The stripe of a module, assigning the next one on first use.
--
-- The demo keeps one flat 'localRegion' rather than a per-declaration
-- 'Registry.RegionLayout': its display shows raw indices directly, and the
-- canonicity of its elaborated terms already holds with the flat region
-- (see 'localRegion'), so it trades the reopening-clash-freedom of regions
-- for small printable names.
registerModule :: Raw.VarIdent -> Registry -> (Registry, Foil.NameRange)
registerModule name registry =
  case Registry.registerUnit name registry of
    (registry', i) -> (registry', stripeRange i)

-- | Where stripe @i@ lies, under the demo's layout.
stripeRange :: StripeIndex -> Foil.NameRange
stripeRange = Registry.stripeRange mlttStripes

-- * Interpreting a program

-- | Interpret a program: order its modules by their imports, then check each.
interpretProgram :: Raw.Program -> [CommandResult]
interpretProgram (Raw.AProgram _loc units) = interpretUnits units

-- | Interpret units gathered from any number of sources.
--
-- The telescopes are resolved over all of them at once, exactly as the imports
-- are, so a module may include a telescope declared in another file.
interpretUnits :: [Raw.Unit] -> [CommandResult]
interpretUnits units = case resolveUnits units of
  Left err      -> [Failed err]
  Right modules -> interpretModules modules

-- | Interpret modules whose includes have already been resolved.
--
-- Build order is computed over all of them at once, so a module may import one
-- declared in another file, or later in the same file.
interpretModules :: [Raw.Module] -> [CommandResult]
interpretModules modules = case buildOrder modules of
  Left err      -> [Failed err]
  Right ordered -> goModules emptyRegistry emptyEnv ordered

-- | Check each module in turn, in the growing top-level scope.
--
-- A module's parameters are elaborated once here, before its declarations, so
-- that a parameter block that does not resolve is reported once rather than
-- against every declaration that would have been checked under it.
goModules :: Foil.Distinct n => Registry -> Env n -> [Raw.Module] -> [CommandResult]
goModules _registry _env [] = []
goModules registry env (m : ms) =
    withCheckedModule (checkModule range env m) $ \_ext env' results ->
      results <> goModules registry' env' ms
  where
    (registry', range) = registerModule (moduleName m) registry

-- * Separate checking and linking

-- | A module checked on its own: its final environment, at an existential
-- scope index, together with the evidence that everything it added to the
-- scope it started from lies inside its stripe. Two of these over the same
-- start can be linked; see 'linkModules'.
data CheckedModule c where
  CheckedModule
    :: Foil.DExt c n
    => Blocks.ExtWithin c n
    -> Env n
    -> [CommandResult]
    -> CheckedModule c

-- | Open a checked module's existential package.
withCheckedModule
  :: CheckedModule c
  -> (forall n. Foil.DExt c n => Blocks.ExtWithin c n -> Env n -> [CommandResult] -> r)
  -> r
withCheckedModule (CheckedModule ext env results) cont = cont ext env results

-- | The results a checked module reported.
resultsOf :: CheckedModule c -> [CommandResult]
resultsOf cm = withCheckedModule cm (\_ _ results -> results)

-- | Check one module against an environment of already checked modules.
--
-- Nothing here depends on any sibling: the module sees only what it imports,
-- and its declarations take the names its stripe dictates, so two modules
-- with no import path between them can be checked in either order — or in
-- parallel — and produce identical results.
--
-- A module's parameters are elaborated once here, before its declarations, so
-- that a parameter block that does not resolve is reported once rather than
-- against every declaration that would have been checked under it.
checkModule
  :: forall c. Foil.Distinct c
  => Foil.NameRange     -- ^ The module's stripe, from the registry.
  -> Env c              -- ^ Environment holding what its imports export.
  -> Raw.Module
  -> CheckedModule c
checkModule range env m =
  case validateParams env' (moduleParams m) of
    Just err -> CheckedModule (Blocks.extWithinRefl range) env' [entered, Failed err]
    Nothing ->
      withDecls (ModuleEnv (Blocks.beginBlock range) env') (moduleParams m) [] (moduleDecls m) $
        \me results ->
          CheckedModule (Blocks.blockExt (moduleBlock me))
                        (finishModule (moduleName m) (moduleEnv me))
                        (entered : results)
  where
    entered = EnteredModule (renderVarIdent (moduleName m))
    -- An import contributes the exporting module's public names, under the
    -- spellings it exported them with. Nothing else crosses a module boundary.
    env' = env
      { envDeclared = Map.unions
          [ Map.findWithDefault Map.empty x (envModules env)
          | Raw.AnImport _ x <- moduleImports m ]
      , envExports = Map.empty
      , envClosedOver = Map.empty
      }

-- | Check a module against the environment of an already checked one,
-- composing the evidence, so that a chain of modules — each importing the
-- previous — presents itself as one checked unit over the chain's base.
-- The chain's results accumulate.
--
-- This is what lets two chains over a shared base be checked in parallel
-- and then linked as wholes: fold each chain with this, then 'linkModules'.
checkModuleAfter
  :: Foil.NameRange     -- ^ The next module's stripe, from the registry.
  -> CheckedModule c    -- ^ The chain so far.
  -> Raw.Module
  -> CheckedModule c
checkModuleAfter range (CheckedModule ext env results) m =
  case checkModule range env m of
    CheckedModule ext' env' results' ->
      CheckedModule (Blocks.composeExtWithin ext ext') env' (results <> results')

-- | Link two units checked independently against the same environment — two
-- modules, or two chains folded with 'checkModuleAfter'.
--
-- The two scopes share exactly the names of the common environment — the
-- amalgamated part, identified rather than renamed apart — and extend it
-- only within their reservations, so the whole disjointness obligation is
-- one sweep over two range sets ('Blocks.withDisjointUnion'). Each side's
-- tables are then sunk into the union, and the total maps are merged with
-- 'Blocks.unionNameMaps'.
--
-- No module registration happens here: each side's 'envModules' already
-- records everything it checked ('finishModule'), so the union of the two
-- suffices. The result is an environment a further module can be checked in,
-- exactly as if the two sides had been checked in sequence.
linkModules
  :: forall c r
   . CheckedModule c    -- ^ The first unit.
  -> CheckedModule c    -- ^ The second unit.
  -> (forall k. Foil.Distinct k => Env k -> r)
  -> Either BuildError r
linkModules a b cont = do
  linked <- linkChecked a b
  withCheckedModule linked (\_ env _ -> Right (cont env))

-- | Link two units into one, keeping the evidence, so the result links
-- further: a whole build folds through this, wave by wave.
linkChecked :: CheckedModule c -> CheckedModule c -> Either BuildError (CheckedModule c)
linkChecked (CheckedModule extA envA rsA) (CheckedModule extB envB rsB) =
  case Blocks.withDisjointUnion extA extB (ctxScope (envCtx envA)) (ctxScope (envCtx envB))
         (\scope union extK ->
            CheckedModule extK (mergeEnvs union scope envA envB) (rsA <> rsB)) of
    Nothing -> Left "linking: reserved name ranges overlap"
    Just r  -> Right r

-- | Merge the environments of two linked units; see 'linkModules' for why
-- nothing but the union is needed.
mergeEnvs
  :: (Foil.Ext n k, Foil.Ext m k, Foil.Distinct k)
  => Blocks.ScopeUnion n m k -> Foil.Scope k -> Env n -> Env m -> Env k
mergeEnvs union scope envA envB = Env
  { envCtx      = Ctx scope
      (Blocks.unionNameMaps union
        (sunkTo scope (ctxTypes (envCtx envA)))
        (sunkTo scope (ctxTypes (envCtx envB))))
      (Blocks.unionNameMaps union
        (sunkTo scope (ctxDefs (envCtx envA)))
        (sunkTo scope (ctxDefs (envCtx envB))))
  , envDeclared = Map.empty
  , envExports  = Map.empty
  , envModules  = Map.union
      (getCompose (sunkTo scope (Compose (envModules envA))))
      (getCompose (sunkTo scope (Compose (envModules envB))))
  , envDisplay  = Blocks.unionNameMaps union (envDisplay envA) (envDisplay envB)
  , envManifest = Map.empty
  , envClosedOver = Map.empty
  }

-- | 'Foil.sink1', with the target index determined by a scope the
-- caller already holds, so that the wanted constraints match the givens of a
-- linking continuation.
sunkTo
  :: (Functor f, Foil.Sinkable e, Foil.DExt n l)
  => Foil.Scope l -> f (e n) -> f (e l)
sunkTo _scope = Foil.sink1

-- | Record what a module exported, once it is checked.
finishModule :: Raw.VarIdent -> Env l -> Env l
finishModule name env =
  env { envModules = Map.insert name (envExports env) (envModules env) }

-- | Exactly two of something.
--
-- A declaration that elaborates a type and a value, or a term and its type,
-- asks 'withElaborated' for both at once. Using this rather than a list is what
-- makes "elaborated the wrong number of terms" unrepresentable instead of an
-- @error@ in an unreachable branch.
data Two a = Two a a
  deriving (Functor, Foldable, Traversable)

-- | Allocate a module's parameters, extending the environment with them.
--
-- Parameters are allocated in 'localRegion', below every stripe, so they can
-- never collide with a declaration's name — which is what used to force them
-- to be re-allocated per declaration. They are still elaborated afresh for
-- each declaration, but now only for simplicity: a parameter block is a few
-- small terms, and re-elaborating it keeps 'withDecls' a plain fold.
--
-- A parameter is nameable by its bare spelling and is not exported, which is
-- exactly what 'extendEnv' does for a private declaration.
--
-- A /manifest/ parameter binds nothing. Its value is elaborated in the module's
-- own scope, before any of the block's binders, and recorded in 'envManifest',
-- so the spelling stands for that term wherever it is used. Two things follow,
-- and both are the point of the arrangement. A value cannot mention a bound
-- field of the block, since no such name is in scope where it is elaborated,
-- which is the admissibility condition for a refinement enforced by scoping
-- rather than tested. And nothing is ever discharged over a manifest field,
-- since 'discharge' only ever sees the telescope, which such a field is not in.
withParams
  :: forall n r. Foil.Distinct n
  => Env n
  -> [Raw.Param]
  -> (String -> r)        -- ^ A parameter's type or value did not resolve.
  -> (forall p. Foil.DExt n p
        => ParamTelescope Raw.BNFC'Position n p -> Env p -> r)
  -> r
withParams env0 params onErr cont =
  case foldM manifest (envManifest env0)
         [(loc, x, ty, v) | Raw.AManifest loc x ty v <- params] of
    Left err    -> onErr err
    Right table -> go env0 { envManifest = table } params cont
  where
    -- The manifest values, in order, each elaborated with the ones before it in
    -- scope: an earlier manifest field is an abbreviation for an ambient term,
    -- so naming it is naming that term and is no dependence on the block.
    manifest table (loc, name, rawTy, rawValue) =
      let ctx = envCtx env0
          elaborate = tryToTerm'WithIn localRegion (ctxScope ctx)
                        (visibleAt [] (envDeclared env0)) table
       in case (elaborate rawTy, elaborate rawValue) of
            (Left err, _) -> Left (dependsOnUnfixed name err)
            (_, Left err) -> Left (dependsOnUnfixed name err)
            (Right rawTy', Right raw) ->
              let ty = desugar rawTy'
                  value = desugar raw
               in case check ctx ty (Universe Raw.BNFC'NoPosition)
                       >> check ctx value ty of
                    Left err -> Left err
                    Right () -> Right (Map.insert name (inferable loc ty value) table)

    -- Resolution puts a manifest value wherever its spelling occurs, which may
    -- be the head of an application, and the checker is bidirectional: 'infer'
    -- has nothing to say about a bare λ. Such a value goes in ascribed, and the
    -- ascription is stripped by 'whnf', so nothing but 'infer' notices. Every
    -- other form infers as it stands and is left alone, so that a value reads
    -- unchanged when a message shows it.
    inferable loc ty value@Lam{} = Ann loc value ty
    inferable _loc _ty value     = value

    -- A field can only be fixed when everything its type and value mention is
    -- fixed too, since both are elaborated before any of the block's binders.
    -- That is the admissibility condition, and this is what it looks like when
    -- it fails: the name that did not resolve is a field of this very block.
    dependsOnUnfixed name err@(UnresolvedName x _)
      | x `elem` [f | Raw.AParam _ f _ <- params] =
          "cannot fix " <> prettyVarIdent name <> ": it depends on "
            <> prettyVarIdent x <> ", which is not fixed"
      | otherwise = notInScope err

    go :: forall p. Foil.Distinct p
       => Env p
       -> [Raw.Param]
       -> (forall q. Foil.DExt p q
             => ParamTelescope Raw.BNFC'Position p q -> Env q -> r)
       -> r
    go env [] k = k TelescopeEmpty env
    go env (Raw.AManifest{} : rest) k = go env rest k
    go env (Raw.AParam _loc name rawTy : rest) k =
      case tryToTerm'WithIn localRegion (ctxScope ctx)
             (visibleAt [] (envDeclared env)) (envManifest env) rawTy of
        Left err -> onErr (notInScope err)
        Right raw ->
          let ty = desugar raw
           in withVarBinder localRegion ctx ty $ \ctx' binder ->
                go (extendEnv ctx' binder name Private env) rest $ \tele envQ ->
                  k (TelescopeCons name ty binder tele) envQ
      where
        ctx = envCtx env

-- | Elaborate a module's parameter types, reporting the first that fails.
validateParams :: Foil.Distinct n => Env n -> [Raw.Param] -> Maybe TypeError
validateParams env params = withParams env params Just (\_tele _envP -> Nothing)

-- | Split the visible spellings into a table of names and a table of terms,
-- putting the module's parameters back into references to its own
-- declarations.
--
-- A declaration is closed at the point it is defined, so a later one in the
-- same module refers to a constant that expects the parameters it was closed
-- over. Rather than making the source apply them, each spelling that reaches
-- such a constant is moved to the terms table of the conversion
-- ('tryToTerm'With'), where it stands for the constant applied to those
-- parameters. This happens during resolution, so no second pass over the
-- elaborated term is needed.
--
-- The table of names is consulted first, so a local binder or a parameter
-- shadowing the spelling wins, and nothing can be captured. Outside the
-- declaring module the table of terms is empty, which is right: a client is
-- handed a closed constant and instantiates it as it likes.
splitVisible
  :: Env p
  -> Table (Foil.Name p)
  -> (Table (Foil.Name p), Table (Term p))
splitVisible envP visible =
    (Map.difference visible expanded, expanded)
  where
    -- A manifest field wins over a declaration of the same spelling, exactly as
    -- a bound parameter does.
    expanded = Map.union (envManifest envP) parametrised
    parametrised = Map.mapMaybe expand visible
    closedOver = Map.elems (envClosedOver envP)

    expand name
      | Just ps@(_ : _) <- listToMaybe [ps' | (ps', x) <- closedOver, x == name]
      , Just args <- traverse (`Map.lookup` envDeclared envP) ps
      = Just (foldl' apply (Var name) args)
      | otherwise = Nothing

    apply f x = App Raw.BNFC'NoPosition f (Var x)

-- | Report parameters a declaration needs that it is not being closed over.
--
-- With the computed set this cannot arise, since that set is closed. It is the
-- answer for a caller that supplies a set of its own.
needsParameters :: [Raw.VarIdent] -> TypeError
needsParameters names =
  "declaration needs module parameters it is not closed over: "
    <> intercalate ", " (map prettyVarIdent names)

-- | Report an identifier that did not resolve, with any near spellings.
notInScope :: UnresolvedName Raw.VarIdent -> TypeError
notInScope (UnresolvedName x inScope) =
  case suggestions x inScope of
    []    -> "not in scope: " <> prettyVarIdent x
    hints -> "not in scope: " <> prettyVarIdent x
               <> "; did you mean " <> intercalate ", " (map prettyVarIdent hints) <> "?"

-- | Everything a block of declarations is checked in: the module's
-- 'Blocks.Block' — the stripe its names are allocated from, paired with the
-- linking evidence — and the environment. The scope indices are the module's
-- starting scope @c@ and the current scope @n@.
data ModuleEnv c n = ModuleEnv
  { moduleBlock :: Blocks.Block c n
  , moduleEnv   :: Env n
  }

-- | Check a block of declarations at a namespace path.
--
-- The path is lexical, so a nested @namespace@ is just a recursive call with a
-- longer path, and leaving it needs no bookkeeping: the qualified names stay in
-- 'envDeclared' and the bare spellings were never stored, only computed by
-- 'visibleAt'.
--
-- Every declaration is checked with the module's parameters in scope, and a
-- @def@ is then discharged over the ones it uses, so that what is added to the
-- environment lives in the parameter-free scope the module started in.
withDecls
  :: forall c n r. Foil.Distinct n
  => ModuleEnv c n
  -> [Raw.Param]          -- ^ The parameters of the enclosing module.
  -> Path                 -- ^ The namespace path these declarations sit at.
  -> [Raw.Decl]
  -> (forall l. Foil.DExt n l => ModuleEnv c l -> [CommandResult] -> r)
  -> r
withDecls me _params _path [] cont = cont me []
withDecls me params path (decl : decls) cont = case decl of

  Raw.DeclDef loc name over ty value        -> define loc Public name over ty value
  Raw.DeclPrivateDef loc name over ty value -> define loc Private name over ty value

  Raw.DeclNamespace _loc name inner ->
    withDecls me params (path <> segments name) inner $ \meInner innerResults ->
      withDecls meInner params path decls $ \meAfter rest ->
        cont meAfter (innerResults <> rest)

  Raw.DeclOpen _loc name ->
    withDecls me { moduleEnv = env { envDeclared = openNamespace (qualify path name) (envDeclared env) } }
              params path decls cont

  Raw.DeclCheck _loc rawTerm rawType ->
    withParams env params (continue . Failed) $ \_tele envP ->
      withElaborated envP (Two rawTerm rawType) $ \(Two term ty) ->
        case check (envCtx envP) ty universe >> check (envCtx envP) term ty of
          Left err -> continue (Failed err)
          Right () -> continue (Checked (display envP term) (display envP ty))

  Raw.DeclCompute _loc rawTerm ->
    withParams env params (continue . Failed) $ \_tele envP ->
      withElaborated envP (Identity rawTerm) $ \(Identity term) ->
        let ctxP = envCtx envP
         in case infer ctxP term of
              Left err  -> continue (Failed err)
              Right _ty -> continue
                (Computed (display envP (nf (ctxScope ctxP) (ctxDefs ctxP) term)))

  where
    universe = Universe Raw.BNFC'NoPosition
    env = moduleEnv me

    -- Continue with the remaining declarations, with one result in front.
    continue result = withDecls me params path decls $ \me' rest ->
      cont me' (result : rest)

    -- Convert some raw terms, or report the identifiers that do not resolve.
    --
    -- The terms come and go in a container of the caller's choosing, so a
    -- declaration that needs two of them asks with 'Two' and is handed back a
    -- 'Two'.
    withElaborated
      :: forall p f. (Foil.Distinct p, Traversable f)
      => Env p -> f Raw.Term -> (f (Term p) -> r) -> r
    withElaborated envP raws k =
      let (names, terms) = splitVisible envP (visibleAt path (envDeclared envP))
       in case traverse (tryToTerm'WithIn localRegion (ctxScope (envCtx envP)) names terms) raws of
            Left err -> continue (Failed (notInScope err))
            Right ts -> k (fmap desugar ts)

    define loc visibility name over rawType rawValue =
      withParams env params (continue . Failed) $ \tele envP ->
        withElaborated envP (Two rawType rawValue) $ \(Two ty value) ->
          case check (envCtx envP) ty universe >> check (envCtx envP) value ty of
            Left err -> continue (Failed err)
            Right () ->
              -- The discharged pair is well-typed by construction: abstracting a
              -- checked term over a variable of a checked type is Π- and
              -- λ-introduction, so it is not checked again here.
              case discharge loc (ctxScope (envCtx env)) tele Nothing ty value of
                Left missing -> continue (Failed (needsParameters missing))
                Right (Discharged ty' value' over') ->
                  case checkDischarge over over' of
                    Left err -> continue (Failed err)
                    Right () ->
                      -- A top-level constant is an ordinary name in the
                      -- growing scope. It is allocated from the module's
                      -- block, which steps the linking evidence in the same
                      -- motion, so nothing can escape the stripe.
                      Blocks.withFreshInBlock (moduleBlock me) (ctxScope (envCtx env)) $ \binder block' ->
                        let ctx' = extend (envCtx env) binder ty' (Just value')
                            full = qualify path name
                            extended = extendEnv ctx' binder full visibility env
                            env' = extended
                              { envClosedOver = Map.insert full
                                  (over', Foil.nameOf binder)
                                  (envClosedOver extended) }
                         in withDecls (ModuleEnv block' env') params path decls $ \me'' rest ->
                              cont me''
                                (Defined (renderVarIdent full) (map renderVarIdent over') : rest)

-- * An interactive session

-- | A read–eval–print session: a module that never ends. The session holds
-- a 'ModuleEnv' at an existential scope index, so each step picks up exactly
-- where the previous one stopped, allocating from one interactive stripe.
data Repl c where
  Repl :: Foil.DExt c n => ModuleEnv c n -> Repl c

-- | Start a session over an environment of already checked (or loaded)
-- modules, allocating in the given stripe.
beginRepl :: Foil.Distinct c => Foil.NameRange -> Env c -> Repl c
beginRepl range env = Repl (ModuleEnv (Blocks.beginBlock range) env)

-- | Feed one input — any run of declarations, including @check@ and
-- @compute@ — to the session.
--
-- A redefinition allocates a new name and rebinds the spelling, GHCi-style:
-- a term that already refers to the old binding keeps it, since withholding
-- a spelling touches no term.
replStep :: SourceText -> Repl c -> (Repl c, [CommandResult])
replStep input (Repl me) = case parseDecls input of
  Left err -> (Repl me, [Failed ("parse error: " <> err)])
  Right decls ->
    withDecls me [] [] decls $ \me' results -> (Repl me', results)

-- | Parse and interpret one source.
--
-- >>> let report = mapM_ (putStrLn . renderResult) . either error id . interpret
-- >>> report (sourceLines ["module M (A : 𝕌) (x : A)", "def k : A → A := λ y ⇒ y", "def one : A := x"])
-- module M
--   ✓ defined k over (A)
--   ✓ defined one over (A, x)
--
-- Each declaration is discharged over the parameters it uses and no others, so
-- what a client sees is a closed definition it applies for itself.
interpret :: SourceText -> Either ParseError [CommandResult]
interpret input = interpretProgram <$> parseProgram input

-- | Parse and interpret several named sources.
--
-- Each source is parsed on its own, so a syntax error is reported against the
-- line of the file it is in rather than against a concatenation of them all.
-- The units are pooled afterwards, which is what lets one file import a module
-- or include a telescope declared in another.
interpretSources :: [(FilePath, SourceText)] -> Either ParseError [CommandResult]
interpretSources sources = interpretUnits . concat <$> traverse parseSource sources
  where
    parseSource (path, input) = case parseProgram input of
      Left err                       -> Left (path <> ":" <> err)
      Right (Raw.AProgram _loc units) -> Right units

