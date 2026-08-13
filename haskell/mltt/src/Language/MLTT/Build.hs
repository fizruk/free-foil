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
-- result: every built module's exports are in scope, and the session
-- allocates from the first stripe the build left free.
module Language.MLTT.Build (
  BuildMode (..),
  buildModules,
  buildModulesWith,
  buildSources,
  buildSourcesWith,
  sessionOver,
  buildMain,
) where

import           Control.Concurrent       (forkIO, newEmptyMVar, putMVar,
                                           takeMVar)
import           Control.Exception        (evaluate)
import           Control.Monad            (foldM, forM, forM_, unless, when)
import qualified Control.Monad.Foil       as Foil
import           Data.Char                (isSpace)
import           Data.Function            (on)
import           Data.List                (foldl', groupBy, isPrefixOf, sortOn,
                                           stripPrefix)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           System.Directory         (createDirectoryIfMissing,
                                           doesFileExist)
import           System.Exit              (exitFailure)
import           System.FilePath          ((</>))
import           System.IO                (hFlush, isEOF, stdout)

import           Language.MLTT.Artifact
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (parseProgram)
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
    Right (mode, cacheDir, interactive, paths) -> do
      sources <- case paths of
        [] | not interactive -> (\input -> [("<stdin>", input)]) <$> getContents
        _  -> mapM (\path -> (,) path <$> readFile path) paths
      result <- buildSourcesWith mode cacheDir sources $ \registry env results -> do
        mapM_ (putStrLn . renderResult) results
        if interactive
          then True <$ runRepl (sessionOver registry env)
          else pure (succeeded results)
      case result of
        Left err -> putStrLn err >> exitFailure
        Right ok -> unless ok exitFailure

parseArgs :: [String] -> Either String (BuildMode, Maybe FilePath, Bool, [FilePath])
parseArgs = fmap done . foldM step (Sequential, Nothing, False, [])
  where
    done (m, c, i, ps) = (m, c, i, reverse ps)
    step (m, c, i, ps) = \case
      "--mode=sequential" -> Right (Sequential, c, i, ps)
      "--mode=linked"     -> Right (Linked, c, i, ps)
      "--mode=parallel"   -> Right (Parallel, c, i, ps)
      "--repl"            -> Right (m, c, True, ps)
      arg
        | Just dir <- stripPrefix "--cache=" arg -> Right (m, Just dir, i, ps)
        | "--" `isPrefixOf` arg -> Left ("unknown option: " <> arg <> usage)
        | otherwise -> Right (m, c, i, arg : ps)
    usage = "\nusage: mltt [--mode=sequential|linked|parallel] [--cache=DIR] [--repl] [FILES...]"

-- | Begin a session over a build. Every built module's exports are in scope,
-- as if the session's module imported them all, and names are allocated from
-- the first stripe the build left free — the registry is append-only, so its
-- size names that stripe.
sessionOver :: Foil.Distinct c => Registry -> Env c -> Repl c
sessionOver registry env =
  beginRepl (stripeRange (StripeIndex (Map.size registry)))
            env { envDeclared = Map.unions (Map.elems (envModules env)) }

-- | The loop itself: one 'replStep' per line, until end of input. Blank
-- lines are skipped, and results are rendered exactly like the builder's.
runRepl :: Repl c -> IO ()
runRepl = loop
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
            else do
              let (s', results) = replStep line s
              mapM_ (putStrLn . renderResult) results
              loop s'

-- | How to schedule the checking.
data BuildMode = Sequential | Linked | Parallel
  deriving (Eq, Show)

-- | Parse several named sources and build them; see 'buildModules'.
buildSources
  :: BuildMode -> Maybe FilePath -> [(FilePath, String)]
  -> IO (Either String [CommandResult])
buildSources mode cacheDir sources =
  buildSourcesWith mode cacheDir sources (\_ _ results -> pure results)

-- | 'buildSources', handing the continuation the outcome; see
-- 'buildModulesWith'.
buildSourcesWith
  :: BuildMode -> Maybe FilePath -> [(FilePath, String)]
  -> (forall c. Foil.Distinct c => Registry -> Env c -> [CommandResult] -> IO r)
  -> IO (Either String r)
buildSourcesWith mode cacheDir sources k =
  case traverse parseSource sources of
    Left err -> pure (Left err)
    Right ms -> buildModulesWith mode cacheDir (concat ms) k
  where
    parseSource (path, input) = case parseProgram input of
      Left err                    -> Left (path <> ":" <> err)
      Right (Raw.AProgram _ms ms) -> Right ms

-- | The environment a build ends in, its scope index hidden.
data BuiltEnv where
  BuiltEnv :: Foil.Distinct c => Env c -> BuiltEnv

-- | Build a set of modules.
buildModules
  :: BuildMode -> Maybe FilePath -> [Raw.Module]
  -> IO (Either String [CommandResult])
buildModules mode cacheDir modules =
  buildModulesWith mode cacheDir modules (\_ _ results -> pure results)

-- | 'buildModules', handing the continuation the environment the build ends
-- in — at its existential scope index — together with the registry, so a
-- session can be started over the result ('sessionOver').
buildModulesWith
  :: BuildMode -> Maybe FilePath -> [Raw.Module]
  -> (forall c. Foil.Distinct c => Registry -> Env c -> [CommandResult] -> IO r)
  -> IO (Either String r)
buildModulesWith mode cacheDir modules k =
  case buildOrder modules of
    Left err -> pure (Left err)
    Right ordered -> do
      forM_ cacheDir (createDirectoryIfMissing True)
      let registry = foldl' (\r m -> fst (registerModule (moduleName m) r))
                            emptyRegistry ordered
          waves = case mode of
            Sequential -> [[m] | m <- ordered]
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
       => Registry -> Env c -> Map Raw.VarIdent ContentHash -> [[Raw.Module]]
       -> IO (Either String ([(Raw.VarIdent, [CommandResult])], BuiltEnv))
    go _ env _ [] = pure (Right ([], BuiltEnv env))
    go registry env hashes (wave : rest) = do
      units <- produceWave registry env hashes wave
      let hashes' = foldr (\(_, a, _) -> Map.insert (artifactModule a) (artifactHash a))
                          hashes units
          results = [(artifactModule a, rs) | (_, a, rs) <- units]
      case foldM1 linkChecked [cm | (cm, _, _) <- units] of
        Left err     -> pure (Left err)
        Right linked ->
          withCheckedModule linked $ \_ env' _ ->
            fmap (\(more, built) -> (results <> more, built))
              <$> go registry env' hashes' rest

    foldM1 f (x : xs) = foldM f x xs
    foldM1 _ []       = error "impossible: an empty wave"

    -- Check (or load) each module of a wave against the same base
    -- environment; under 'Parallel', each on its own thread.
    produceWave
      :: Foil.Distinct c
      => Registry -> Env c -> Map Raw.VarIdent ContentHash -> [Raw.Module]
      -> IO [(CheckedModule c, ModuleArtifact, [CommandResult])]
    produceWave registry env hashes wave
      | mode == Parallel = do
          vars <- forM wave $ \m -> do
            var <- newEmptyMVar
            _ <- forkIO $ do
              unit@(_, _, rs) <- produce registry env hashes m
              _ <- evaluate (length (show rs))   -- do the work on this thread
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
            then either (const Nothing) Just . readArtifact <$> readFile (path dir)
            else pure Nothing
      case cached of
        Just a
          | artifactSource a == source
          , Right cm <- loadArtifact hashes range env a
          -> pure (cm, a, [LoadedModule (prettyVarIdent name)])
        _ -> do
          let cm = checkModule range env m
              a  = makeArtifact name idx source importHashes cm
              rs = resultsOf cm
          forM_ cacheDir $ \dir ->
            when (succeeded rs) $
              writeFile (path dir) (renderArtifact a)
          pure (cm, a, rs)

-- | Group modules, already in topological order, into dependency waves: a
-- module's wave is one past the deepest wave among its imports, so the
-- members of a wave are mutually independent.
wavesOf :: [Raw.Module] -> [[Raw.Module]]
wavesOf ordered = map (map snd) (groupBy ((==) `on` fst) (sortOn fst levelled))
  where
    levelled = [(levelOf m, m) | m <- ordered]
    levels :: Map Raw.VarIdent Int
    levels = foldl' step Map.empty ordered
    step acc m = Map.insert (moduleName m) (computeLevel acc m) acc
    computeLevel acc m = 1 + maximum
      (0 : [ Map.findWithDefault 0 x acc | Raw.AnImport _ x <- moduleImports m ])
    levelOf m = Map.findWithDefault 0 (moduleName m) levels
