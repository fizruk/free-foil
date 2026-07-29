{-# LANGUAGE DataKinds           #-}
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
import           Data.List                    (intercalate)
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import qualified Data.Set                     as Set
import           Language.MLTT.Eval
import           Language.MLTT.FreeFoilConfig (intToVarIdent)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve
import qualified Language.MLTT.Syntax.Abs     as Raw
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
  -> Bool                   -- ^ Is it public?
  -> Env n
  -> Env l
extendEnv ctx binder full public env = Env
  { envCtx      = ctx
  , envDeclared = Map.insert full name (Foil.sinkContainer (envDeclared env))
  , envExports  = (if public then Map.insert full name else id)
                    (Foil.sinkContainer (envExports env))
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
  | Defined String            -- ^ @def@ succeeded, for the fully qualified name.
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
  Defined name       -> "  ✓ defined " <> name
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
moduleName (Raw.AModule _ name _ _) = name

-- | The imports of a module.
moduleImports :: Raw.Module -> [Raw.Import]
moduleImports (Raw.AModule _ _ imports _) = imports

-- | The declarations of a module.
moduleDecls :: Raw.Module -> [Raw.Decl]
moduleDecls (Raw.AModule _ _ _ decls) = decls

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
goModules :: Foil.Distinct n => Env n -> [Raw.Module] -> [CommandResult]
goModules _env [] = []
goModules env (m : ms) =
    withDecls env' [] (moduleDecls m) $ \env'' results ->
      EnteredModule (prettyVarIdent (moduleName m))
        : results
        <> goModules (finishModule (moduleName m) env'') ms
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

-- | Check a block of declarations at a namespace path.
--
-- The path is lexical, so a nested @namespace@ is just a recursive call with a
-- longer path, and leaving it needs no bookkeeping: the qualified names stay in
-- 'envDeclared' and the bare spellings were never stored, only computed by
-- 'visibleAt'.
withDecls
  :: forall n r. Foil.Distinct n
  => Env n
  -> Path                 -- ^ The namespace path these declarations sit at.
  -> [Raw.Decl]
  -> (forall l. Foil.DExt n l => Env l -> [CommandResult] -> r)
  -> r
withDecls env _path [] cont = cont env []
withDecls env path (decl : decls) cont = case decl of

  Raw.DeclDef loc name ty value        -> define True loc name ty value
  Raw.DeclPrivateDef loc name ty value -> define False loc name ty value

  Raw.DeclNamespace _loc name inner ->
    withDecls env (path <> segments name) inner $ \envInner innerResults ->
      withDecls envInner path decls $ \envAfter rest ->
        cont envAfter (innerResults <> rest)

  Raw.DeclOpen _loc name ->
    withDecls (env { envDeclared = openNamespace (qualify path name) (envDeclared env) })
              path decls cont

  Raw.DeclCheck _loc rawTerm rawType -> withElaborated [rawTerm, rawType] $ \case
    Right [term, ty] ->
      case check (envCtx env) ty universe >> check (envCtx env) term ty of
        Left err -> continue (Failed err)
        Right () -> continue (Checked (display' term) (display' ty))
    _ -> error "impossible: elaborated the wrong number of terms"

  Raw.DeclCompute _loc rawTerm -> withElaborated [rawTerm] $ \case
    Right [term] -> case infer (envCtx env) term of
      Left err  -> continue (Failed err)
      Right _ty -> continue (Computed (display' (nf (ctxScope ctx) (ctxDefs ctx) term)))
    _ -> error "impossible: elaborated the wrong number of terms"

  where
    ctx = envCtx env
    universe = Universe Raw.BNFC'NoPosition
    display' = display env
    visible = visibleAt path (envDeclared env)

    -- Continue with the remaining declarations, with one result in front.
    continue result = withDecls env path decls $ \env' rest -> cont env' (result : rest)

    -- Resolve and convert a batch of raw terms, or report the first spelling
    -- that does not resolve. Checking before converting is what keeps an
    -- out-of-scope name a diagnostic rather than a crash.
    withElaborated raws k = case concatMap (unresolved visible) raws of
      (x : _) -> continue (Failed (notInScope x))
      []      -> k (Right (map (desugar . toTerm' (ctxScope ctx) visible) raws))

    notInScope x = "not in scope: " <> prettyVarIdent x

    define public loc name rawType rawValue = withElaborated [rawType, rawValue] $ \case
      Right [ty, value] ->
        case check ctx ty universe >> check ctx value ty of
          Left err -> continue (Failed err)
          Right () ->
            withDefinition ctx ty value $ \ctx' binder ->
              let full = qualify path name
                  env' = extendEnv ctx' binder full public env
               in withDecls env' path decls $ \env'' rest ->
                    cont env'' (Defined (prettyVarIdent full) : rest)
      _ -> error "impossible: elaborated the wrong number of terms"
      where _ = loc

-- | Show a raw identifier as it was written.
prettyVarIdent :: Raw.VarIdent -> String
prettyVarIdent (Raw.VarIdent x) = x

-- | Parse and interpret one source.
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
