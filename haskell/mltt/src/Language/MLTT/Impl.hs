{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
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
import           Control.Monad.Free.Foil      (AST (Var), UnresolvedName (..))
import           Data.List                    (foldl', intercalate)
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import qualified Data.Set                     as Set
import           Language.MLTT.Eval
import           Language.MLTT.FreeFoilConfig (intToVarIdent)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Interner
import           Language.MLTT.Resolve
import qualified Language.MLTT.Syntax.Abs     as Raw
import qualified Language.MLTT.Syntax.Print   as Raw
import           Language.MLTT.Telescope
import           Language.MLTT.Typecheck
import           System.Exit                  (exitFailure)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds

-- * The elaboration environment

-- | Everything carried from one declaration to the next.
--
-- Note that this is /not/ indexed by a scope. A top-level declaration is an
-- interned constant and not a name, so nothing here grows a scope, nothing has
-- to be sunk, and the interpreter needs no continuation-passing to thread one.
-- The foil index appears below only where there are local variables: inside a
-- declaration, and for a module's parameters.
data Env = Env
  { envCtx      :: Ctx Raw.BNFC'Position Foil.VoidS
    -- ^ The type and the value of each constant. Both are closed.
  , envDeclared :: Table (ConstId, [Raw.VarIdent])
    -- ^ Fully qualified names reachable in the module being checked, each with
    -- the module parameters that declaration was closed over. Those are put
    -- back at every use; see 'Language.MLTT.Interner.internTerm'.
  , envExports  :: Table (ConstId, [Raw.VarIdent])
    -- ^ Those declarations of the current module that are public. They are
    -- exported with an empty parameter list: a client sees a closed constant
    -- and applies it itself.
  , envModules  :: Map Raw.VarIdent (Table (ConstId, [Raw.VarIdent]))
    -- ^ What each module checked so far exports.
  , envNames    :: Map ConstId Raw.VarIdent
    -- ^ What each constant is called, for printing.
  , envNext     :: ConstId
    -- ^ The next identifier to hand out.
  }

-- | An empty environment, before any module is checked.
emptyEnv :: Env
emptyEnv = Env emptyCtx Map.empty Map.empty Map.empty Map.empty 0

-- | Intern a checked declaration as a new constant.
internDefinition
  :: Raw.VarIdent           -- ^ Its fully qualified name.
  -> Visibility             -- ^ Does it leave the module?
  -> [Raw.VarIdent]         -- ^ The module parameters it was closed over.
  -> Term Foil.VoidS        -- ^ Its type, closed.
  -> Term Foil.VoidS        -- ^ Its value, closed.
  -> Env
  -> Env
internDefinition full visibility over ty value env = env
  { envCtx      = withConst i ty value (envCtx env)
  , envDeclared = Map.insert full (i, over) (envDeclared env)
  , envExports  = export visibility full (i, []) (envExports env)
  , envNames    = Map.insert i full (envNames env)
  , envNext     = i + 1
  }
  where
    i = envNext env

-- | Print a term, showing constants by name and bound variables by their index.
--
-- The 'Foil.NameMap' names what is free in the term, which for a checked
-- declaration is nothing at all: it is closed. Only a term being checked under
-- module parameters has free names, and 'display' is given their names then.
display
  :: Foil.Distinct n
  => Env -> Foil.NameMap n Raw.VarIdent -> Term n -> String
display env free =
  Raw.printTree . nameConsts (envNames env) . fromTermWith intToVarIdent free

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

-- | Check each module in turn.
--
-- A module's parameters are elaborated once here, before its declarations, so
-- that a parameter block that does not resolve is reported once rather than
-- against every declaration that would have been checked under it.
goModules :: Env -> [Raw.Module] -> [CommandResult]
goModules _env [] = []
goModules env (m : ms) = EnteredModule (prettyVarIdent (moduleName m)) :
    case validateParams env' (moduleParams m) of
      Just err -> Failed err : goModules env ms
      Nothing ->
        let (env'', results) = goDecls env' (moduleParams m) [] (moduleDecls m)
         in results <> goModules (finishModule (moduleName m) env'') ms
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
finishModule :: Raw.VarIdent -> Env -> Env
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

-- | What a module's parameters give a declaration being checked under them.
data Params p = Params
  { paramsTelescope :: Telescope Raw.BNFC'Position Foil.VoidS p
  , paramsCtx       :: Ctx Raw.BNFC'Position p
  , paramsTable     :: Table (Foil.Name p)  -- ^ For elaboration.
  , paramsNames     :: Foil.NameMap p Raw.VarIdent  -- ^ For printing.
  }

-- | Allocate a module's parameters.
--
-- These are the only names the interpreter allocates: everything at the top
-- level is a constant. They are allocated afresh for each declaration, which
-- costs a few small terms and keeps each declaration's scope to its own
-- parameters.
withParams
  :: forall r. Env
  -> [Raw.Param]
  -> (String -> r)        -- ^ A parameter's type did not resolve.
  -> (forall p. Foil.DExt Foil.VoidS p => Params p -> r)
  -> r
withParams env params0 onErr cont = go emptyParams params0
  where
    emptyParams = Params TelescopeEmpty (envCtx env) Map.empty Foil.emptyNameMap

    go :: forall p. Foil.DExt Foil.VoidS p => Params p -> [Raw.Param] -> r
    go acc [] = cont acc
    go acc (Raw.AParam _loc name rawTy : rest) =
      case elaborate env (paramsCtx acc) (paramsTable acc) [] rawTy of
        Left err -> onErr err
        Right ty ->
          withVarBinder (paramsCtx acc) ty $ \ctx' binder ->
            go Params
              { paramsTelescope = appendParam (paramsTelescope acc) name ty binder
              , paramsCtx       = ctx'
              , paramsTable     = Map.insert name (Foil.nameOf binder)
                                    (Foil.sinkContainer (paramsTable acc))
              , paramsNames     = Foil.addNameBinder binder name (paramsNames acc)
              } rest

-- | Elaborate a module's parameter types, reporting the first that fails.
validateParams :: Env -> [Raw.Param] -> Maybe String
validateParams env params = withParams env params Just (\_ -> Nothing)

-- | Elaborate a raw term.
--
-- A module parameter resolves to a name and a top-level declaration to a
-- constant, so the conversion is given both tables. It consults the names
-- first, which is what makes a parameter shadow a declaration of the same
-- spelling, and it puts the module parameters back at every use: the entry for
-- a declaration is its constant already applied to them.
elaborate
  :: Foil.Distinct p
  => Env
  -> Ctx Raw.BNFC'Position p
  -> Table (Foil.Name p)        -- ^ The module parameters in scope.
  -> Path
  -> Raw.Term
  -> Either String (Term p)
elaborate env ctx paramTable path raw =
  case tryToTerm'With (ctxScope ctx) paramTable constants raw of
    Left err -> Left (notInScope err)
    Right t  -> Right (desugar t)
  where
    constants = Map.fromList
      [ (spelling, foldl' apply (Const Raw.BNFC'NoPosition i) args)
      | (spelling, (i, ps)) <- Map.toList (visibleAt path (envDeclared env))
      , Just args <- [traverse (`Map.lookup` paramTable) ps]
      ]
    apply f x = App Raw.BNFC'NoPosition f (Var x)

-- | Check a block of declarations at a namespace path.
--
-- The path is lexical, so a nested @namespace@ is just a recursive call with a
-- longer path, and leaving it needs no bookkeeping: the qualified names stay in
-- 'envDeclared' and the bare spellings were never stored, only computed by
-- 'visibleAt'.
goDecls
  :: Env
  -> [Raw.Param]          -- ^ The parameters of the enclosing module.
  -> Path                 -- ^ The namespace path these declarations sit at.
  -> [Raw.Decl]
  -> (Env, [CommandResult])
goDecls env _params _path [] = (env, [])
goDecls env params path (decl : decls) = case decl of

  Raw.DeclDef loc name over ty value        -> define loc Public name over ty value
  Raw.DeclPrivateDef loc name over ty value -> define loc Private name over ty value

  Raw.DeclNamespace _loc name inner ->
    let (envInner, innerResults) = goDecls env params (path <> segments name) inner
        (envAfter, rest)         = goDecls envInner params path decls
     in (envAfter, innerResults <> rest)

  Raw.DeclOpen _loc name ->
    goDecls (env { envDeclared = openNamespace (qualify path name) (envDeclared env) })
            params path decls

  Raw.DeclCheck _loc rawTerm rawType ->
    withParams env params (continue . Failed) $ \ps ->
      withElaborated ps (Two rawTerm rawType) $ \(Two term ty) ->
        case check (paramsCtx ps) ty universe >> check (paramsCtx ps) term ty of
          Left err -> continue (Failed err)
          Right () -> continue
            (Checked (display env (paramsNames ps) term)
                     (display env (paramsNames ps) ty))

  Raw.DeclCompute _loc rawTerm ->
    withParams env params (continue . Failed) $ \ps ->
      withElaborated ps (Identity rawTerm) $ \(Identity term) ->
        let ctxP = paramsCtx ps
         in case infer ctxP term of
              Left err  -> continue (Failed err)
              Right _ty -> continue (Computed (display env (paramsNames ps)
                (nf (ctxScope ctxP) (ctxConsts ctxP) term)))

  where
    universe = Universe Raw.BNFC'NoPosition

    -- Continue with the remaining declarations, with one result in front.
    continue result =
      let (env', rest) = goDecls env params path decls in (env', result : rest)

    continueWith env0 result =
      let (env', rest) = goDecls env0 params path decls in (env', result : rest)

    withElaborated
      :: forall p f. (Foil.Distinct p, Traversable f)
      => Params p -> f Raw.Term -> (f (Term p) -> (Env, [CommandResult]))
      -> (Env, [CommandResult])
    withElaborated ps raws k =
      case traverse (elaborate env (paramsCtx ps) (paramsTable ps) path) raws of
        Left err -> continue (Failed err)
        Right ts -> k ts

    define loc visibility name over rawType rawValue =
      withParams env params (continue . Failed) $ \ps ->
        withElaborated ps (Two rawType rawValue) $ \(Two ty value) ->
          case check (paramsCtx ps) ty universe >> check (paramsCtx ps) value ty of
            Left err -> continue (Failed err)
            Right () ->
              -- Closing over the parameters leaves a term with no free names at
              -- all, so what is interned is closed by type and not by
              -- discipline. That is the whole point of this variant.
              case discharge loc Foil.emptyScope (paramsTelescope ps) Nothing ty value of
                Left missing -> continue (Failed (needsParameters missing))
                Right (Discharged ty' value' over') ->
                  case checkDischarge over over' of
                    Left err -> continue (Failed err)
                    Right () -> continueWith
                      (internDefinition full visibility over' ty' value' env)
                      (Defined (prettyVarIdent full) (map prettyVarIdent over'))
      where
        full = qualify path name

-- | Add a parameter to the end of a telescope.
appendParam
  :: (Foil.Distinct i, Foil.DExt i l)
  => Telescope Raw.BNFC'Position n i
  -> Raw.VarIdent
  -> Term i
  -> Foil.NameBinder i l
  -> Telescope Raw.BNFC'Position n l
appendParam TelescopeEmpty name ty binder =
  TelescopeCons name ty binder TelescopeEmpty
appendParam (TelescopeCons name' ty' binder' rest) name ty binder =
  TelescopeCons name' ty' binder' (appendParam rest name ty binder)

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
