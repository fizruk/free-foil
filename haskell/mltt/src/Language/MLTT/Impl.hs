{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
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

import           Control.Monad                (foldM)
import qualified Control.Monad.Foil           as Foil
import           Data.Functor.Identity        (Identity (..))
import           Control.Monad.Free.Foil      (UnresolvedName (..))
import           Data.List                    (intercalate)
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import qualified Data.Set                     as Set
import           Language.MLTT.Eval
import           Language.MLTT.FreeFoilConfig (intToVarIdent)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Telescope
import           Language.MLTT.Typecheck
import           System.Exit                  (exitFailure)

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
  }

-- | An empty environment, before any module is checked.
emptyEnv :: Env Foil.VoidS
emptyEnv = Env emptyCtx Map.empty Map.empty Map.empty Foil.emptyNameMap

-- | Extend an environment with one top-level definition.
--
-- Every map is a container of sinkables, so widening them is \(O(1)\); only the
-- new entry is inserted, and only the map of modules has its spine walked.
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
  , envModules  = fmap Foil.sinkContainer (envModules env)
  , envDisplay  = Foil.addNameBinder binder full (envDisplay env)
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
  | Defined String [String]   -- ^ @def@ succeeded, for the fully qualified name
                              -- and the module parameters it was discharged over.
  | Checked String String     -- ^ @check@ succeeded, for a term and its type.
  | Computed String           -- ^ @compute@ succeeded, with the normal form.
  | Failed String             -- ^ The declaration was rejected.
  deriving (Eq, Show)

-- | Did everything succeed?
succeeded :: [CommandResult] -> Bool
succeeded = all $ \case
  Failed _ -> False
  _        -> True

-- | Render a result the way the executable prints it.
renderResult :: CommandResult -> String
renderResult = \case
  EnteredModule name -> "module " <> name
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
  Right ordered -> goModules emptyEnv ordered

-- | Check each module in turn, in the growing top-level scope.
--
-- A module's parameters are elaborated once here, before its declarations, so
-- that a parameter block that does not resolve is reported once rather than
-- against every declaration that would have been checked under it.
goModules :: Foil.Distinct n => Env n -> [Raw.Module] -> [CommandResult]
goModules _env [] = []
goModules env (m : ms) = EnteredModule (prettyVarIdent (moduleName m)) :
    case validateParams env' (moduleParams m) of
      Just err -> Failed err : goModules env ms
      Nothing ->
        withDecls env' (moduleParams m) [] (moduleDecls m) $ \env'' results ->
          results <> goModules (finishModule (moduleName m) env'') ms
  where
    -- An import contributes the exporting module's public names, under the
    -- spellings it exported them with. Nothing else crosses a module boundary.
    env' = env
      { envDeclared = Map.unions
          [ Map.findWithDefault Map.empty x (envModules env)
          | Raw.AnImport _ x <- moduleImports m ]
      , envExports = Map.empty
      }

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
-- Parameters are allocated afresh for each declaration rather than once for the
-- module, because a declaration is added to the module's own scope after being
-- discharged, and a name allocated there would otherwise collide with a
-- parameter allocated before it. Re-elaborating a parameter block costs a few
-- small terms and buys a scope that grows only by definitions.
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
  case tryToTerm' (ctxScope ctx) (visibleAt [] (envDeclared env)) rawTy of
    Left err -> onErr (notInScope err)
    Right raw ->
      let ty = desugar raw
       in withVarBinder ctx ty $ \ctx' binder ->
            withParams (extendEnv ctx' binder name Private env) rest onErr $
              \tele envP -> cont (TelescopeCons name ty (ctxScope ctx) binder tele) envP
  where
    ctx = envCtx env

-- | Elaborate a module's parameter types, reporting the first that fails.
validateParams :: Foil.Distinct n => Env n -> [Raw.Param] -> Maybe String
validateParams env params = withParams env params Just (\_tele _envP -> Nothing)

-- | Report an identifier that did not resolve, with any near spellings.
notInScope :: UnresolvedName Raw.VarIdent -> String
notInScope (UnresolvedName x inScope) =
  case suggestions x inScope of
    []    -> "not in scope: " <> prettyVarIdent x
    hints -> "not in scope: " <> prettyVarIdent x
               <> "; did you mean " <> intercalate ", " (map prettyVarIdent hints) <> "?"

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
  :: forall n r. Foil.Distinct n
  => Env n
  -> [Raw.Param]          -- ^ The parameters of the enclosing module.
  -> Path                 -- ^ The namespace path these declarations sit at.
  -> [Raw.Decl]
  -> (forall l. Foil.DExt n l => Env l -> [CommandResult] -> r)
  -> r
withDecls env _params _path [] cont = cont env []
withDecls env params path (decl : decls) cont = case decl of

  Raw.DeclDef loc name over ty value        -> define loc Public name over ty value
  Raw.DeclPrivateDef loc name over ty value -> define loc Private name over ty value

  Raw.DeclNamespace _loc name inner ->
    withDecls env params (path <> segments name) inner $ \envInner innerResults ->
      withDecls envInner params path decls $ \envAfter rest ->
        cont envAfter (innerResults <> rest)

  Raw.DeclOpen _loc name ->
    withDecls (env { envDeclared = openNamespace (qualify path name) (envDeclared env) })
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

    -- Continue with the remaining declarations, with one result in front.
    continue result = withDecls env params path decls $ \env' rest -> cont env' (result : rest)

    -- Convert some raw terms, or report the identifiers that do not resolve.
    --
    -- The terms come and go in a container of the caller's choosing, so a
    -- declaration that needs two of them asks with 'Two' and is handed back a
    -- 'Two'.
    withElaborated
      :: forall p f. (Foil.Distinct p, Traversable f)
      => Env p -> f Raw.Term -> (f (Term p) -> r) -> r
    withElaborated envP raws k =
      case traverse (tryToTerm' (ctxScope (envCtx envP)) (visibleAt path (envDeclared envP))) raws of
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
              let Discharged ty' value' over' = discharge loc tele ty value
               in case checkDischarge over over' of
                    Left err -> continue (Failed err)
                    Right () ->
                      withDefinition (envCtx env) ty' value' $ \ctx' binder ->
                        let full = qualify path name
                            env' = extendEnv ctx' binder full visibility env
                         in withDecls env' params path decls $ \env'' rest ->
                              cont env''
                                (Defined (prettyVarIdent full) (map prettyVarIdent over') : rest)

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

-- | Read modules from the given files, or from standard input if none are
-- given, and interpret them.
defaultMain :: [FilePath] -> IO ()
defaultMain paths = do
  sources <- case paths of
    [] -> (\input -> [("<stdin>", input)]) <$> getContents
    _  -> mapM (\path -> (,) path <$> readFile path) paths
  case interpretSources sources of
    Left err -> do
      putStrLn err
      exitFailure
    Right results -> do
      mapM_ (putStrLn . renderResult) results
      if succeeded results then return () else exitFailure
