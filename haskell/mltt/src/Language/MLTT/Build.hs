{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | A builder over the module machinery: collect modules, order them by
-- imports, and build one of three ways —
--
-- * 'Sequential': one module after another in topological order, each
--   absorbed into a growing environment; the classic driver.
-- * 'Linked': modules grouped into dependency waves; each wave's modules are
--   checked separately against the same base and then linked as units.
-- * 'Parallel': the same waves, with each wave's modules checked on
--   concurrently forked threads.
--
-- All three produce the same results, declaration names included, because
-- names come from the registry's stripes and elaboration is canonical; the
-- spec pins the equality. 'Sequential' is 'Linked' with singleton waves, so
-- one driver serves all three.
--
-- With a cache directory, each successfully checked module's artifact is
-- written beside the build, and a module whose printed source and imports
-- are unchanged is loaded instead of checked ('LoadedModule' in the
-- results). Staleness is content-defined, so a rebuilt dependency whose
-- declarations came out unchanged does not dirty its dependants (early
-- cutoff). A cached module's @check@ and @compute@ commands are not re-run:
-- the cache reconstructs environments, not output.
--
-- With @--repl@, the build is followed by an interactive session over its
-- result. The session starts seeing nothing, like any module: an @import@
-- brings a built module's exports into scope, or loads a module (and its
-- missing imports) from the cache mid-session. The session allocates from
-- the first stripe the build left free.
module Language.MLTT.Build (
  BuildMode (..),
  BuildOptions (..),
  SessionMode (..),
  buildModules,
  buildModulesWith,
  buildSources,
  buildSourcesWith,
  sessionOver,
  replImport,
  buildMain,
) where

import           Control.Concurrent       (forkIO, newEmptyMVar, putMVar,
                                           takeMVar)
import           Control.DeepSeq          (force)
import           Control.Exception        (evaluate)
import           Control.Monad            (foldM, forM, forM_, unless, when)
import qualified Control.Monad.Foil       as Foil
import qualified Control.Monad.Foil.Blocks as Blocks
import           Control.Monad.Foil.Registry (StripeIndex (..))
import qualified Data.ByteString          as BS
import qualified Data.ByteString.Lazy     as BSL
import           Data.Char                (isSpace)
import           Data.Function            (on)
import           Data.Functor.Compose     (Compose (..))
import           Data.List                (foldl', isPrefixOf, sortOn,
                                           stripPrefix)
import           Data.List.NonEmpty       (NonEmpty (..))
import qualified Data.List.NonEmpty       as NonEmpty
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           System.Directory         (createDirectoryIfMissing,
                                           doesFileExist)
import           System.Exit              (exitFailure)
import           System.FilePath          ((</>))
import           System.IO                (hFlush, isEOF, stdout)

import           Control.Monad.Free.Foil.Artifact (storedConstants)
import           Language.MLTT.Artifact
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText (..), parseImports,
                                               parseProgram)
import           Language.MLTT.Resolve    (prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs as Raw
import qualified Language.MLTT.Syntax.Print as Raw

-- | The executable's entry point:
-- @mltt [--mode=sequential|linked|parallel] [--cache=DIR] [--repl] [FILES…]@,
-- reading standard input when no files are given.
--
-- With @--repl@, the files are built first and a session is started over the
-- result; standard input then belongs to the session, so no files means an
-- empty environment rather than a source on standard input. The session is
-- entered even if some declarations failed — the failures were reported, and
-- what did check is there to poke at.
buildMain :: [String] -> IO ()
buildMain args =
  case parseArgs args of
    Left err -> putStrLn err >> exitFailure
    Right opts -> do
      sources <- case optFiles opts of
        [] | optSession opts == BatchOnly ->
          (\input -> [("<stdin>", SourceText input)]) <$> getContents
        paths -> mapM (\path -> (,) path . SourceText <$> readFile path) paths
      result <- buildSourcesWith (optMode opts) (optCache opts) sources $
        \registry env results -> do
          mapM_ (putStrLn . renderResult) results
          case optSession opts of
            Interactive -> True <$ runRepl (optCache opts) (sessionOver registry env)
            BatchOnly   -> pure (succeeded results)
      case result of
        Left err -> putStrLn err >> exitFailure
        Right ok -> unless ok exitFailure

-- | Whether the build is followed by an interactive session (@--repl@).
data SessionMode = BatchOnly | Interactive
  deriving (Eq, Show)

-- | What the command line asked for.
data BuildOptions = BuildOptions
  { optMode    :: BuildMode
  , optCache   :: Maybe FilePath
  , optSession :: SessionMode
  , optFiles   :: [FilePath]
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either ErrorMessage BuildOptions
parseArgs = fmap done . foldM step (BuildOptions Sequential Nothing BatchOnly [])
  where
    done opts = opts { optFiles = reverse (optFiles opts) }
    step opts = \case
      "--mode=sequential" -> Right opts { optMode = Sequential }
      "--mode=linked"     -> Right opts { optMode = Linked }
      "--mode=parallel"   -> Right opts { optMode = Parallel }
      "--repl"            -> Right opts { optSession = Interactive }
      arg
        | Just dir <- stripPrefix "--cache=" arg -> Right opts { optCache = Just dir }
        | "--" `isPrefixOf` arg -> Left ("unknown option: " <> arg <> usage)
        | otherwise -> Right opts { optFiles = arg : optFiles opts }
    usage = "\nusage: mltt [--mode=sequential|linked|parallel] [--cache=DIR] [--repl] [FILES...]"

-- | Begin a session over a build. The session is a module that never ends,
-- and like any module it starts seeing nothing: an @import@ brings a built
-- module's exports into scope ('replImport'). Names are allocated from the
-- first stripe the build left free — the registry is append-only, so its
-- size names that stripe.
sessionOver :: Foil.Distinct c => Registry -> Env c -> Repl c
sessionOver registry env =
  beginRepl (stripeRange (StripeIndex (Map.size registry)))
            env { envDeclared   = Map.empty
                , envExports    = Map.empty
                , envClosedOver = Map.empty
                }

-- | One interactive @import@.
--
-- A module the session's world already holds — built before the session, or
-- imported earlier — contributes its exports to what the session can name,
-- and nothing else: the import is resolution, exactly as in a module
-- header, except that a later import rebinds a spelling an earlier one
-- brought in, the way a later @def@ rebinds one.
--
-- A module the world does not hold is loaded from the cache: the module and
-- its missing imports, dependency-first, each artifact loaded over the
-- session's current scope at its recorded stripe, so the session's evidence
-- grows by the imports' stripes ('Blocks.composeExtWithin') and the session
-- keeps allocating in its own stripe over the enlarged scope
-- ('Blocks.resumeBlock'). Staleness is checked exactly as in the builder:
-- an artifact's recorded import hashes must agree with the artifacts its
-- imports load from.
replImport :: Maybe FilePath -> Raw.VarIdent -> Repl c -> IO (Repl c, [CommandResult])
replImport cacheDir name repl@(Repl me)
  | Map.member name (envModules (moduleEnv me)) = pure (resolutionImport name repl)
  | otherwise = case cacheDir of
      Nothing ->
        pure (repl, [Failed ("unknown module " <> prettyVarIdent name
                              <> ", and no cache directory to load it from")])
      Just dir -> do
        gathered <- gatherArtifacts dir (moduleEnv me) name
        pure $ case gathered of
          Left err                  -> (repl, [Failed err])
          Right (artifacts, hashes) -> loadImports hashes artifacts name repl

-- | Bring an already-checked module's exports into the session's view.
resolutionImport :: Raw.VarIdent -> Repl c -> (Repl c, [CommandResult])
resolutionImport name (Repl (ModuleEnv block env)) =
  case Map.lookup name (envModules env) of
    Nothing ->
      ( Repl (ModuleEnv block env)
      , [Failed ("unknown module " <> prettyVarIdent name)] )
    Just exports ->
      ( Repl (ModuleEnv block env { envDeclared = exports <> envDeclared env })
      , [Imported (renderVarIdent name)] )

-- | Collect, dependency-first, the artifacts an import has to load: the
-- module itself and every import of it the session's world does not hold.
-- For an import the world does hold, only its artifact's content hash is
-- read, which is what a dependant's staleness check compares against.
gatherArtifacts
  :: FilePath -> Env n -> Raw.VarIdent
  -> IO (Either ErrorMessage ([ModuleArtifact], Map Raw.VarIdent ContentHash))
gatherArtifacts dir env = go [] ([], Map.empty)
  where
    artifactPath name = dir </> prettyVarIdent name <> ".mltta"

    readArtifactFor name = do
      exists <- doesFileExist (artifactPath name)
      if not exists
        then pure (Left ("unknown module " <> prettyVarIdent name
                          <> ": not in this session's world, and no artifact at "
                          <> artifactPath name))
        else either (\e -> Left ("artifact for " <> prettyVarIdent name <> ": " <> e)) Right
               . decodeArtifact . BSL.fromStrict <$> BS.readFile (artifactPath name)

    go trail acc@(loads, hashes) name
      | name `elem` trail =
          pure (Left ("import cycle in cached artifacts through " <> prettyVarIdent name))
      | Map.member name hashes = pure (Right acc)
      | Map.member name (envModules env) = fmap recordHash <$> readArtifactFor name
      | otherwise = do
          ea <- readArtifactFor name
          case ea of
            Left err -> pure (Left err)
            Right a -> do
              deeper <- foldM (visit (name : trail)) (Right acc)
                              [x | (x, _) <- artifactImports a]
              pure $ case deeper of
                Left err -> Left err
                Right (loads', hashes') ->
                  Right ( loads' <> [a]
                        , Map.insert (artifactModule a) (artifactHash a) hashes' )
      where
        recordHash a = (loads, Map.insert name (artifactHash a) hashes)

    visit trail acc name = case acc of
      Left err   -> pure (Left err)
      Right acc' -> go trail acc' name

-- | The session's own view of the world: what it can name, what it has
-- defined, and what those definitions were closed over. Loading an artifact
-- rewires exactly these three tables to the loaded module's view, so an
-- import saves them, sinks them along each load, and puts them back.
data SessionView n = SessionView
  { viewDeclared   :: Map Raw.VarIdent (Foil.Name n)
  , viewExports    :: Map Raw.VarIdent (Foil.Name n)
  , viewClosedOver :: Map Raw.VarIdent ([Raw.VarIdent], Foil.Name n)
  }

sessionView :: Env n -> SessionView n
sessionView env = SessionView (envDeclared env) (envExports env) (envClosedOver env)

sinkView :: Foil.DExt n l => SessionView n -> SessionView l
sinkView (SessionView decls exports closed) =
  SessionView (Foil.sink1 decls) (Foil.sink1 exports)
              (getCompose (Foil.sink1 (Compose closed)))

-- | The importing fold's carrier: the session's block over its base, the
-- environment after the loads so far, and the session's view sunk along.
data Importing c where
  Importing
    :: Foil.DExt c n
    => Blocks.Block c n -> Env n -> SessionView n -> Importing c

-- | Load the gathered artifacts over the session, dependency-first, and
-- bring the imported module's exports into the session's view.
loadImports
  :: Map Raw.VarIdent ContentHash -> [ModuleArtifact] -> Raw.VarIdent
  -> Repl c -> (Repl c, [CommandResult])
loadImports hashes artifacts name (Repl me) =
  case foldM step (Importing (moduleBlock me) (moduleEnv me) (sessionView (moduleEnv me))) artifacts of
    Left err -> (Repl me, [Failed err])
    Right (Importing block env view) ->
      let exports = Map.findWithDefault Map.empty name (envModules env)
          env' = env
            { envDeclared   = exports <> viewDeclared view
            , envExports    = viewExports view
            , envClosedOver = viewClosedOver view
            }
       in ( Repl (ModuleEnv block env')
          , [LoadedModule (renderVarIdent (artifactModule a)) | a <- artifacts]
              <> [Imported (renderVarIdent name)] )
  where
    step (Importing block env view) a = do
      cm <- loadArtifact hashes (storedConstants (artifactLayout a)) env a
      withCheckedModule cm $ \ext env' _ ->
        case Blocks.resumeBlock (Blocks.blockRange block)
               (Blocks.composeExtWithin (Blocks.blockExt block) ext) of
          Nothing     -> error "impossible: composition dropped the session's own range"
          Just block' -> Right (Importing block' env' (sinkView view))

-- | The loop itself: one step per line, until end of input. A line of
-- imports goes through 'replImport'; anything else is a 'replStep'. Blank
-- lines are skipped, and results are rendered exactly like the builder's.
runRepl :: Maybe FilePath -> Repl c -> IO ()
runRepl cacheDir = loop
  where
    loop s = do
      putStr "mltt> "
      hFlush stdout
      end <- isEOF
      if end
        then putStrLn ""
        else do
          line <- getLine
          if all isSpace line
            then loop s
            else case parseImports (SourceText line) of
              Right imports@(_ : _) -> do
                (s', results) <- foldM importOne (s, []) imports
                mapM_ (putStrLn . renderResult) results
                loop s'
              _ -> do
                let (s', results) = replStep (SourceText line) s
                mapM_ (putStrLn . renderResult) results
                loop s'

    importOne (s, results) (Raw.AnImport _ name) = do
      (s', more) <- replImport cacheDir name s
      pure (s', results <> more)

-- | How to schedule the checking.
data BuildMode = Sequential | Linked | Parallel
  deriving (Eq, Show)

-- | Parse several named sources and build them; see 'buildModules'.
buildSources
  :: BuildMode -> Maybe FilePath -> [(FilePath, SourceText)]
  -> IO (Either BuildError [CommandResult])
buildSources mode cacheDir sources =
  buildSourcesWith mode cacheDir sources (\_ _ results -> pure results)

-- | 'buildSources', handing the continuation the outcome; see
-- 'buildModulesWith'.
buildSourcesWith
  :: BuildMode -> Maybe FilePath -> [(FilePath, SourceText)]
  -> (forall c. Foil.Distinct c => Registry -> Env c -> [CommandResult] -> IO r)
  -> IO (Either BuildError r)
buildSourcesWith mode cacheDir sources k =
  case resolveUnits . concat =<< traverse parseSource sources of
    Left err      -> pure (Left err)
    Right modules -> buildModulesWith mode cacheDir modules k
  where
    parseSource (path, input) = case parseProgram input of
      Left err                        -> Left (path <> ":" <> err)
      Right (Raw.AProgram _loc units) -> Right units

-- | The environment a build ends in, its scope index hidden.
data BuiltEnv where
  BuiltEnv :: Foil.Distinct c => Env c -> BuiltEnv

-- | Build a set of modules.
buildModules
  :: BuildMode -> Maybe FilePath -> [Raw.Module]
  -> IO (Either BuildError [CommandResult])
buildModules mode cacheDir modules =
  buildModulesWith mode cacheDir modules (\_ _ results -> pure results)

-- | 'buildModules', handing the continuation the environment the build ends
-- in — at its existential scope index — together with the registry, so a
-- session can be started over the result ('sessionOver').
buildModulesWith
  :: BuildMode -> Maybe FilePath -> [Raw.Module]
  -> (forall c. Foil.Distinct c => Registry -> Env c -> [CommandResult] -> IO r)
  -> IO (Either BuildError r)
buildModulesWith mode cacheDir modules k =
  case buildOrder modules of
    Left err -> pure (Left err)
    Right ordered -> do
      forM_ cacheDir (createDirectoryIfMissing True)
      let registry = foldl' (\r m -> fst (registerModule (moduleName m) r))
                            emptyRegistry ordered
          waves = case mode of
            Sequential -> [m :| [] | m <- ordered]
            _          -> wavesOf ordered
          -- Results are reported in topological order whatever the
          -- schedule, so the three modes are comparable verbatim.
          assemble perModule =
            let table = Map.fromListWith (flip (<>)) perModule
             in concat [Map.findWithDefault [] (moduleName m) table | m <- ordered]
      result <- go registry emptyEnv Map.empty waves
      case result of
        Left err -> pure (Left err)
        Right (perModule, BuiltEnv env) ->
          Right <$> k registry env (assemble perModule)
  where
    go :: Foil.Distinct c
       => Registry -> Env c -> Map Raw.VarIdent ContentHash -> [NonEmpty Raw.Module]
       -> IO (Either BuildError ([(Raw.VarIdent, [CommandResult])], BuiltEnv))
    go _ env _ [] = pure (Right ([], BuiltEnv env))
    go registry env hashes (wave : rest) = do
      units <- produceWave registry env hashes wave
      let hashes' = foldr (\(_, a, _) -> Map.insert (artifactModule a) (artifactHash a))
                          hashes units
          results = [(artifactModule a, rs) | (_, a, rs) <- NonEmpty.toList units]
          first :| more = fmap (\(cm, _, _) -> cm) units
      case foldM linkChecked first more of
        Left err     -> pure (Left err)
        Right linked ->
          withCheckedModule linked $ \_ env' _ ->
            fmap (\(later, built) -> (results <> later, built))
              <$> go registry env' hashes' rest

    -- Check (or load) each module of a wave against the same base
    -- environment; under 'Parallel', each on its own thread.
    produceWave
      :: Foil.Distinct c
      => Registry -> Env c -> Map Raw.VarIdent ContentHash -> NonEmpty Raw.Module
      -> IO (NonEmpty (CheckedModule c, ModuleArtifact, [CommandResult]))
    produceWave registry env hashes wave
      | mode == Parallel = do
          vars <- forM wave $ \m -> do
            var <- newEmptyMVar
            _ <- forkIO $ do
              unit@(_, _, rs) <- produce registry env hashes m
              _ <- evaluate (force rs)   -- do the work on this thread
              putMVar var unit
            pure var
          mapM takeMVar vars
      | otherwise = mapM (produce registry env hashes) wave

    produce
      :: Foil.Distinct c
      => Registry -> Env c -> Map Raw.VarIdent ContentHash -> Raw.Module
      -> IO (CheckedModule c, ModuleArtifact, [CommandResult])
    produce registry env hashes m = do
      let name = moduleName m
          idx = Map.findWithDefault (error "impossible: unregistered module")
                                    name registry
          range = stripeRange idx
          source = contentHash (Raw.printTree m)
          importHashes =
            [ (x, h)
            | Raw.AnImport _ x <- moduleImports m
            , Just h <- [Map.lookup x hashes] ]
          path dir = dir </> prettyVarIdent name <> ".mltta"
      cached <- case cacheDir of
        Nothing  -> pure Nothing
        Just dir -> do
          exists <- doesFileExist (path dir)
          if exists
            then either (const Nothing) Just . decodeArtifact . BSL.fromStrict
                   <$> BS.readFile (path dir)
            else pure Nothing
      case cached of
        Just a
          | artifactSource a == source
          , Right cm <- loadArtifact hashes range env a
          -> pure (cm, a, [LoadedModule (renderVarIdent name)])
        _ -> do
          let cm = checkModule range env m
              a  = makeArtifact name range source importHashes cm
              rs = resultsOf cm
          forM_ cacheDir $ \dir ->
            when (succeeded rs) $
              BSL.writeFile (path dir) (encodeArtifact a)
          pure (cm, a, rs)

-- | Group modules, already in topological order, into dependency waves: a
-- module's wave is one past the deepest wave among its imports, so the
-- members of a wave are mutually independent.
wavesOf :: [Raw.Module] -> [NonEmpty Raw.Module]
wavesOf ordered = map (fmap snd) (NonEmpty.groupBy ((==) `on` fst) (sortOn fst levelled))
  where
    levelled = [(levelOf m, m) | m <- ordered]
    levels :: Map Raw.VarIdent Int
    levels = foldl' step Map.empty ordered
    step acc m = Map.insert (moduleName m) (computeLevel acc m) acc
    computeLevel acc m = 1 + maximum
      (0 : [ Map.findWithDefault 0 x acc | Raw.AnImport _ x <- moduleImports m ])
    levelOf m = Map.findWithDefault 0 (moduleName m) levels
