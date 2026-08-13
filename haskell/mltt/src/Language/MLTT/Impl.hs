{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import           Data.Functor.Compose         (Compose (..))
import           Data.Functor.Identity        (Identity (..))
import           Control.Monad.Free.Foil      (AST (Var), UnresolvedName (..))
import           Data.List                    (foldl', intercalate)
import           Data.Map                     (Map)
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
emptyEnv = Env emptyCtx Map.empty Map.empty Map.empty Foil.emptyNameMap Map.empty

-- | Extend an environment with one top-level definition.
--
-- Every map is a container of sinkables, so widening them is a coercion, and
-- only the new entry is inserted. The nested containers (the tables of the
-- module map, the pairs of 'envClosedOver') are sunk through 'Compose', the
-- same idiom 'Foil.sinkContainer' itself uses one level down, so no spine is
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
  , envDeclared = Map.insert full name (Foil.sinkContainer (envDeclared env))
  , envExports  = export visibility full name (Foil.sinkContainer (envExports env))
  , envModules  = getCompose (Foil.sinkContainer (Compose (envModules env)))
  , envDisplay  = Foil.addNameBinder binder full (envDisplay env)
  , envClosedOver = getCompose (Foil.sinkContainer (Compose (envClosedOver env)))
  }
  where
    name = Foil.nameOf binder

-- | Print a term, showing top-level definitions by name and bound variables by
-- their index.
display :: Foil.Distinct n => Env n -> Term n -> String
display env = showTermWith intToVarIdent (envDisplay env)

-- * Results

-- | What interpreting one declaration produced.
data CommandResult
  = EnteredModule String      -- ^ A module was reached in build order.
  | LoadedModule String       -- ^ A module was loaded from its cached
                              -- artifact; its @check@ and @compute@ commands
                              -- are not re-run.
  | Defined String [String]   -- ^ @def@ succeeded, for the fully qualified name
                              -- and the module parameters it was discharged over.
  | Checked String String     -- ^ @check@ succeeded, for a term and its type.
  | Computed String           -- ^ @compute@ succeeded, with the normal form.
  | Failed String             -- ^ The declaration was rejected.
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
  EnteredModule name -> "module " <> name
  LoadedModule name  -> "module " <> name <> " (cached)"
  Defined name []    -> "  ✓ defined " <> name
  Defined name used  -> "  ✓ defined " <> name
                          <> " over (" <> intercalate ", " used <> ")"
  Checked term ty    -> "  ✓ " <> term <> " : " <> ty
  Computed term      -> "  ↦ " <> term
  Failed err         -> "  ✗ " <> err

-- * Build order

-- | Order the modules so that every module comes after the ones it imports.
--
-- Reports an import of a module that is not present, and an import cycle,
-- rather than looping or crashing.
buildOrder :: [Raw.Module] -> Either String [Raw.Module]
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
moduleName (Raw.AModule _ name _ _ _) = name

-- | The parameters of a module.
moduleParams :: Raw.Module -> [Raw.Param]
moduleParams (Raw.AModule _ _ params _ _) = params

-- | The imports of a module.
moduleImports :: Raw.Module -> [Raw.Import]
moduleImports (Raw.AModule _ _ _ imports _) = imports

-- | The declarations of a module.
moduleDecls :: Raw.Module -> [Raw.Decl]
moduleDecls (Raw.AModule _ _ _ _ decls) = decls

-- * Name layout

-- | How many top-level names a module may declare.
stripeSize :: Int
stripeSize = 0x100000

-- | Where the first stripe starts. Below it lies 'localRegion'.
firstStripeBase :: Int
firstStripeBase = stripeSize

-- | The region module parameters and elaboration-time binders live in.
--
-- It lies below every stripe, so nothing here can collide with a
-- declaration's name, and the indices stay small — a discharged type prints
-- as @Π (x0 : 𝕌) → …@ however many declarations precede it. More
-- importantly, allocation inside the region depends only on the region's own
-- content, so elaborating a declaration produces the same term whatever else
-- the ambient scope holds: elaborated terms, and hence artifacts and their
-- hashes, are canonical across worlds.
--
-- The region's budget is spent on syntax, not on computation. Evaluation and
-- type checking allocate their transient names at the whole scope's
-- successor, above every stripe, and nothing rests on those; what lands here
-- is one name per binder /written/ in the declaration being elaborated, plus
-- the parameters, and the region resets between declarations, since
-- elaboration binders live inside terms and never enter the module's scope.
-- So the occupancy bound is the source size of one declaration against a
-- budget of \(2^{20}\). Were it ever exhausted, 'Foil.withFreshIn' fails
-- loudly rather than colliding: the size is a liveness constant, not a
-- soundness assumption, and widening the region relative to the stripes is a
-- policy change confined to these constants.
localRegion :: Foil.NameRange
localRegion = Foil.NameRange 0 (firstStripeBase - 1)

-- | A stripe's position in the registry: which run of 'stripeSize' names a
-- module draws from. Its own type, so that a stripe index cannot be confused
-- with a name, a count, or an offset.
newtype StripeIndex = StripeIndex Int
  deriving (Eq, Ord, Show, Read)

-- | Which stripe each module's declarations live in.
--
-- The assignment is what makes raw names deterministic: a module's
-- declarations are numbered @base@, @base + 1@, … in declaration order,
-- whatever else is checked around it. In a real build this map is persistent
-- — written beside the build products and loaded at start — because cached
-- artefacts survive changes elsewhere in the module graph exactly when the
-- assignment does not move. Here it is threaded through one run, and a test
-- (or a driver) can seed it.
type Registry = Map Raw.VarIdent StripeIndex

-- | The registry before any module has ever been checked.
emptyRegistry :: Registry
emptyRegistry = Map.empty

-- | The stripe of a module, assigning the next one on first use.
-- The registry is append-only, so the next stripe index is its size.
registerModule :: Raw.VarIdent -> Registry -> (Registry, Foil.NameRange)
registerModule name registry = case Map.lookup name registry of
  Just i  -> (registry, stripeRange i)
  Nothing -> let i = StripeIndex (Map.size registry)
              in (Map.insert name i registry, stripeRange i)

-- | Stripe @i@ is the @i@-th run of 'stripeSize' names above 'firstStripeBase'.
stripeRange :: StripeIndex -> Foil.NameRange
stripeRange (StripeIndex i) = Foil.NameRange lo (lo + stripeSize - 1)
  where
    lo = firstStripeBase + i * stripeSize

-- * Interpreting a program

-- | Interpret a program: order its modules by their imports, then check each.
interpretProgram :: Raw.Program -> [CommandResult]
interpretProgram (Raw.AProgram _loc modules) = interpretModules modules

-- | Interpret modules gathered from any number of sources.
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
    entered = EnteredModule (prettyVarIdent (moduleName m))
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
  -> Either String r
linkModules a b cont = do
  linked <- linkChecked a b
  withCheckedModule linked (\_ env _ -> Right (cont env))

-- | Link two units into one, keeping the evidence, so the result links
-- further: a whole build folds through this, wave by wave.
linkChecked :: CheckedModule c -> CheckedModule c -> Either String (CheckedModule c)
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
  , envClosedOver = Map.empty
  }

-- | 'Foil.sinkContainer', with the target index determined by a scope the
-- caller already holds, so that the wanted constraints match the givens of a
-- linking continuation.
sunkTo
  :: (Functor f, Foil.Sinkable e, Foil.DExt n l)
  => Foil.Scope l -> f (e n) -> f (e l)
sunkTo _scope = Foil.sinkContainer

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
withParams
  :: forall n r. Foil.Distinct n
  => Env n
  -> [Raw.Param]
  -> (String -> r)        -- ^ A parameter's type did not resolve.
  -> (forall p. Foil.DExt n p
        => Telescope Raw.BNFC'Position n p -> Env p -> r)
  -> r
withParams env [] _onErr cont = cont TelescopeEmpty env
withParams env (Raw.AParam _loc name rawTy : rest) onErr cont =
  case tryToTerm'In localRegion (ctxScope ctx) (visibleAt [] (envDeclared env)) rawTy of
    Left err -> onErr (notInScope err)
    Right raw ->
      let ty = desugar raw
       in withVarBinder localRegion ctx ty $ \ctx' binder ->
            withParams (extendEnv ctx' binder name Private env) rest onErr $
              \tele envP -> cont (TelescopeCons name ty binder tele) envP
  where
    ctx = envCtx env

-- | Elaborate a module's parameter types, reporting the first that fails.
validateParams :: Foil.Distinct n => Env n -> [Raw.Param] -> Maybe String
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
    (Map.difference visible parametrised, parametrised)
  where
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
needsParameters :: [Raw.VarIdent] -> String
needsParameters names =
  "declaration needs module parameters it is not closed over: "
    <> intercalate ", " (map prettyVarIdent names)

-- | Report an identifier that did not resolve, with any near spellings.
notInScope :: UnresolvedName Raw.VarIdent -> String
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
                                (Defined (prettyVarIdent full) (map prettyVarIdent over') : rest)

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
replStep :: String -> Repl c -> (Repl c, [CommandResult])
replStep input (Repl me) = case parseDecls input of
  Left err -> (Repl me, [Failed ("parse error: " <> err)])
  Right decls ->
    withDecls me [] [] decls $ \me' results -> (Repl me', results)

-- | Parse and interpret one source.
--
-- >>> let report = mapM_ (putStrLn . renderResult) . either error id . interpret
-- >>> report (unlines ["module M (A : 𝕌) (x : A)", "def k : A → A := λ y ⇒ y", "def one : A := x"])
-- module M
--   ✓ defined k over (A)
--   ✓ defined one over (A, x)
--
-- Each declaration is discharged over the parameters it uses and no others, so
-- what a client sees is a closed definition it applies for itself.
interpret :: String -> Either String [CommandResult]
interpret input = interpretProgram <$> parseProgram input

-- | Parse and interpret several named sources.
--
-- Each source is parsed on its own, so a syntax error is reported against the
-- line of the file it is in rather than against a concatenation of them all.
-- The modules are pooled afterwards, which is what lets one file import
-- another.
interpretSources :: [(FilePath, String)] -> Either String [CommandResult]
interpretSources sources = interpretModules . concat <$> traverse parseSource sources
  where
    parseSource (path, input) = case parseProgram input of
      Left err                    -> Left (path <> ":" <> err)
      Right (Raw.AProgram _ms ms) -> Right ms

