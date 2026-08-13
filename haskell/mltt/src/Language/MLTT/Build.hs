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
module Language.MLTT.Build (
  BuildMode (..),
  buildModules,
  buildSources,
  buildMain,
) where

import           Control.Concurrent       (forkIO, newEmptyMVar, putMVar,
                                           takeMVar)
import           Control.Exception        (evaluate)
import           Control.Monad            (foldM, forM, forM_, when)
import qualified Control.Monad.Foil       as Foil
import           Data.List                (groupBy, isPrefixOf, sortOn,
                                           stripPrefix)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           System.Directory         (createDirectoryIfMissing,
                                           doesFileExist)
import           System.Exit              (exitFailure)
import           System.FilePath          ((</>))

import           Language.MLTT.Artifact
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (parseProgram)
import           Language.MLTT.Resolve    (prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs as Raw
import qualified Language.MLTT.Syntax.Print as Raw

-- | The executable's entry point:
-- @mltt [--mode=sequential|linked|parallel] [--cache=DIR] [FILES…]@,
-- reading standard input when no files are given.
buildMain :: [String] -> IO ()
buildMain args =
  case parseArgs args of
    Left err -> putStrLn err >> exitFailure
    Right (mode, cacheDir, paths) -> do
      sources <- case paths of
        [] -> (\input -> [("<stdin>", input)]) <$> getContents
        _  -> mapM (\path -> (,) path <$> readFile path) paths
      result <- buildSources mode cacheDir sources
      case result of
        Left err -> putStrLn err >> exitFailure
        Right results -> do
          mapM_ (putStrLn . renderResult) results
          if succeeded results then pure () else exitFailure

parseArgs :: [String] -> Either String (BuildMode, Maybe FilePath, [FilePath])
parseArgs = fmap done . foldM step (Sequential, Nothing, [])
  where
    done (m, c, ps) = (m, c, reverse ps)
    step (m, c, ps) = \case
      "--mode=sequential" -> Right (Sequential, c, ps)
      "--mode=linked"     -> Right (Linked, c, ps)
      "--mode=parallel"   -> Right (Parallel, c, ps)
      arg
        | Just dir <- stripPrefix "--cache=" arg -> Right (m, Just dir, ps)
        | "--" `isPrefixOf` arg -> Left ("unknown option: " <> arg <> usage)
        | otherwise -> Right (m, c, arg : ps)
    usage = "\nusage: mltt [--mode=sequential|linked|parallel] [--cache=DIR] [FILES...]"

-- | How to schedule the checking.
data BuildMode = Sequential | Linked | Parallel
  deriving (Eq, Show)

-- | Parse several named sources and build them; see 'buildModules'.
buildSources
  :: BuildMode -> Maybe FilePath -> [(FilePath, String)]
  -> IO (Either String [CommandResult])
buildSources mode cacheDir sources =
  case traverse parseSource sources of
    Left err -> pure (Left err)
    Right ms -> buildModules mode cacheDir (concat ms)
  where
    parseSource (path, input) = case parseProgram input of
      Left err                    -> Left (path <> ":" <> err)
      Right (Raw.AProgram _ms ms) -> Right ms

-- | Build a set of modules.
buildModules
  :: BuildMode -> Maybe FilePath -> [Raw.Module]
  -> IO (Either String [CommandResult])
buildModules mode cacheDir modules =
  case buildOrder modules of
    Left err -> pure (Left err)
    Right ordered -> do
      forM_ cacheDir (createDirectoryIfMissing True)
      let registry = foldl (\r m -> fst (registerModule (moduleName m) r))
                           emptyRegistry ordered
          waves = case mode of
            Sequential -> [[m] | m <- ordered]
            _          -> wavesOf ordered
          -- Results are reported in topological order whatever the
          -- schedule, so the three modes are comparable verbatim.
          assemble perModule =
            let table = Map.fromListWith (flip (<>)) perModule
             in concat [Map.findWithDefault [] (moduleName m) table | m <- ordered]
      fmap assemble <$> go registry emptyEnv Map.empty waves
  where
    go :: Foil.Distinct c
       => Registry -> Env c -> Map Raw.VarIdent ContentHash -> [[Raw.Module]]
       -> IO (Either String [(Raw.VarIdent, [CommandResult])])
    go _ _ _ [] = pure (Right [])
    go registry env hashes (wave : rest) = do
      units <- produceWave registry env hashes wave
      let hashes' = foldr (\(_, a, _) -> Map.insert (artifactModule a) (artifactHash a))
                          hashes units
          results = [(artifactModule a, rs) | (_, a, rs) <- units]
      case foldM1 linkChecked [cm | (cm, _, _) <- units] of
        Left err     -> pure (Left err)
        Right linked ->
          withCheckedModule linked $ \_ env' _ ->
            fmap (results <>) <$> go registry env' hashes' rest

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
wavesOf ordered = map (map snd) (groupBy (\a b -> fst a == fst b) (sortOn fst levelled))
  where
    levelled = [(levelOf m, m) | m <- ordered]
    levels :: Map Raw.VarIdent Int
    levels = foldl step Map.empty ordered
    step acc m = Map.insert (moduleName m) (computeLevel acc m) acc
    computeLevel acc m = 1 + maximum
      (0 : [ Map.findWithDefault 0 x acc | Raw.AnImport _ x <- moduleImports m ])
    levelOf m = Map.findWithDefault 0 (moduleName m) levels
