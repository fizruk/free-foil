#!/usr/bin/env stack
{- stack script
   --resolver nightly-2024-08-17
   --package base
   --package containers
   --package process
   --package directory
   --package filepath
-}

-- | @\@since@ tooling for the @free-foil@ package.
--
-- Three modes:
--
-- > scripts/since.hs resolve   -- print "entity<TAB>version" for the whole API
-- > scripts/since.hs apply     -- insert the annotations into the sources
-- > scripts/since.hs check     -- exit 1 if an exported entity has no @since
--
-- @resolve@ dates each entity by the earliest released tag whose sources
-- already declare it. Working from the tags rather than from @git log -S@ is
-- what keeps an entity dated correctly when it moved between modules, which
-- several did in 0.3.0.
--
-- @check@ is the drift guard: it reads the working tree alone and reports every
-- exported entity whose haddock carries no @\@since@.
--
-- The notion of "entity" is the same in both modes: a top-level type signature
-- (each name of a multi-name signature counts), a top-level @data@, @newtype@,
-- @type@, @class@ or @pattern@ declaration, and a class method. Constructors
-- and record fields are left to their type.

{-# LANGUAGE LambdaCase #-}

module Main (main) where

import           Control.Monad    (forM_, unless)
import           Data.Char        (isAlpha, isAlphaNum, isSpace, isUpper)
import           Data.Foldable    (foldl')
import           Data.List        (isInfixOf, isPrefixOf, isSuffixOf, sort,
                                   stripPrefix)
import qualified Data.Map.Strict  as Map
import           Data.Maybe       (fromMaybe, listToMaybe, mapMaybe)
import qualified Data.Set         as Set
import           System.Directory (doesDirectoryExist, listDirectory)
import           System.Environment (getArgs)
import           System.Exit      (exitFailure, exitWith, ExitCode (..))
import           System.FilePath  ((</>), takeExtension)
import           System.IO        (hPutStrLn, readFile', stderr)
import           System.Process   (readProcess, readProcessWithExitCode)

-- | Where the library's sources live, relative to the repository root.
srcRoot :: FilePath
srcRoot = "haskell/free-foil/src"

-- | The released versions, oldest first, each with the git ref holding its
-- sources. 0.3.3 is listed by commit until its tag is pushed; a tag of the
-- same name takes over automatically once it exists.
releases :: [(String, String)]
releases =
  [ ("0.0.1", "v0.0.1")
  , ("0.0.2", "v0.0.2")
  , ("0.0.3", "v0.0.3")
  , ("0.1.0", "v0.1.0")
  , ("0.2.0", "v0.2.0")
  , ("0.3.0", "v0.3.0")
  , ("0.3.1", "v0.3.1")
  , ("0.3.2", "v0.3.2")
  , ("0.3.3", "v0.3.3")
  ]

-- | The version an entity absent from every release belongs to.
unreleasedVersion :: String
unreleasedVersion = "0.4.0"

-- | Modules whose declarations are implementation detail rather than API, and
-- so are not expected to carry @\@since@. These are the compile-time error
-- machinery and the Template Haskell helpers, which are re-exported only as
-- part of an umbrella module.
undocumentedModules :: [FilePath]
undocumentedModules =
  [ "Control/Monad/Foil/Internal/ValidNameBinders.hs"
  , "Control/Monad/Foil/TH/Util.hs"
  , "Control/Monad/Free/Foil/TH/PatternSynonyms.hs"
  ]

-- | Whether a source file is one of 'undocumentedModules'.
isUndocumentedModule :: FilePath -> Bool
isUndocumentedModule path = any (`isSuffixOf` path) undocumentedModules

-- * Entities

-- | A declared name, with the module it is declared in.
data Entity = Entity
  { entityName   :: String
  , entityModule :: FilePath
  , entityLine   :: Int
  } deriving (Eq, Ord, Show)

-- | Whether a module exports everything it declares, or only a list.
data Exports = ExportsAll | ExportsOnly (Set.Set String)

-- | The names a module declares, in source order.
--
-- An indented signature counts as a class method only inside a @class@ body.
-- The same shape inside an @instance@ body is a definition of a method
-- declared elsewhere, and is not an entity of its own.
declarationsOf :: [String] -> [(Int, String)]
declarationsOf ls = go 1 False ls
  where
    go _ _ [] = []
    go i inClass (line : rest) =
      let inClass'
            | "class " `isPrefixOf` line    = True
            | "instance " `isPrefixOf` line = False
            | null (takeWhile isSpace line), not (null (words line)) = False
            | otherwise = inClass
          next = fromMaybe "" (listToMaybe rest)
       in [(i, name) | name <- namesOn inClass' line next]
            ++ go (i + 1) inClass' rest

-- | The entity names a single line declares, given the line after it.
namesOn :: Bool -> String -> String -> [String]
namesOn inClass line next
  | isInstanceEquation             = []
  | Just rest <- keyword "data"    = typeName rest
  | Just rest <- keyword "newtype" = typeName rest
  | Just rest <- keyword "type"    = typeName rest
  | Just rest <- keyword "class"   = typeName rest
  | Just rest <- keyword "pattern" = typeName rest
  | topLevelSignature              = signatureNames line
  | topLevelBareName               = signatureNames line
  | methodSignature                = signatureNames (dropWhile isSpace line)
  | otherwise                      = []
  where
    keyword kw = do
      rest <- stripPrefix (kw ++ " ") line
      pure (dropWhile isSpace (fromMaybe rest (stripPrefix "family " rest)))

    typeName rest = case span isNameChar (dropWhile (== '(') rest) of
      (n@(c : _), _) | isUpper c -> [n]
      _                          -> []

    -- A @type instance@ or @data instance@ defines no new entity.
    isInstanceEquation =
      any (`isPrefixOf` line) ["type instance ", "data instance "]

    -- @f :: ...@ or @f, g :: ...@ at column 0.
    topLevelSignature = startsLower line && "::" `elem` tokensBefore line

    -- @f@ at column 0 with the @::@ on the next line.
    topLevelBareName =
      startsLower line
        && all (\c -> isNameChar c || c == ',' || isSpace c) line
        && not (null (words line))
        && "::" `isPrefixOf` dropWhile isSpace next

    -- A class method: two-space indentation and a signature, inside a class.
    methodSignature =
      inClass
        && "  " `isPrefixOf` line
        && not ("   " `isPrefixOf` line)
        && startsLower (drop 2 line)
        && "::" `elem` tokensBefore (drop 2 line)

    startsLower = \case
      (c : _) -> isAlpha c && not (isUpper c)
      _       -> False

    tokensBefore = words . takeWhile (/= '-')

-- | The names bound by a signature line, which may bind several.
signatureNames :: String -> [String]
signatureNames line = mapMaybe nameOf (splitOn ',' (takeWhile (/= ':') line))
  where
    nameOf s = case span isNameChar (dropWhile isSpace s) of
      (n@(c : _), rest) | isAlpha c, all isSpace rest -> Just n
      _                                               -> Nothing

isNameChar :: Char -> Bool
isNameChar c = isAlphaNum c || c == '_' || c == '\''

splitOn :: Char -> String -> [String]
splitOn sep s = case break (== sep) s of
  (chunk, [])       -> [chunk]
  (chunk, _ : rest) -> chunk : splitOn sep rest

-- | A module's export list, if it has one.
--
-- The header is read from the @module@ keyword to the @where@ that closes it,
-- tracking parenthesis depth, so that a @where@ belonging to some later
-- declaration cannot be mistaken for the end of the header.
exportsOf :: [String] -> Exports
exportsOf ls =
  case break ("module " `isPrefixOf`) (map stripComment ls) of
    (_, [])       -> ExportsAll
    (_, header)   ->
      let body = headerText (unwords header)
       in if '(' `elem` body
            then ExportsOnly (Set.fromList (exportNames body))
            else ExportsAll
  where
    stripComment ('-' : '-' : _) = []
    stripComment (c : cs)        = c : stripComment cs
    stripComment []              = []

    -- Everything up to the @where@ that closes the header. Lazy, so that the
    -- 'unwords' over the rest of the file is never forced past it.
    headerText = go (0 :: Int)
      where
        go _ [] = []
        go depth s@(c : rest)
          | c == '('                  = c : go (depth + 1) rest
          | c == ')'                  = c : go (depth - 1) rest
          | depth == 0, isWhereHere s = []
          | otherwise                 = c : go depth rest
        isWhereHere s = case stripPrefix "where" s of
          Just after -> maybe True (not . isNameChar) (listToMaybe after)
          Nothing    -> False

    exportNames = mapMaybe cleanup . splitOn ',' . drop 1 . dropWhile (/= '(')
    -- An export entry may be prefixed by a namespace keyword, as in
    -- @pattern AnnNode@ or @type (:@:)@.
    cleanup raw =
      let trimmed = dropWhile isSpace raw
          s = filter (/= '(') (takeWhile (/= ')') (dropKeyword trimmed))
       in case span isNameChar s of
            (n@(_ : _), _) -> Just n
            _              -> Nothing
    dropKeyword s = case words s of
      (kw : _) | kw `elem` ["pattern", "type", "data", "module"] ->
        dropWhile isSpace (drop (length kw) s)
      _ -> s

-- | Whether a declaration is exported.
isExported :: Exports -> String -> Bool
isExported ExportsAll         _ = True
isExported (ExportsOnly set) n  = n `Set.member` set

-- * Reading sources

-- | Every Haskell source file under a directory.
haskellFiles :: FilePath -> IO [FilePath]
haskellFiles dir = do
  isDir <- doesDirectoryExist dir
  if not isDir
    then pure []
    else do
      entries <- listDirectory dir
      fmap concat $ traverse (\entry -> do
        let path = dir </> entry
        sub <- doesDirectoryExist path
        if sub
          then haskellFiles path
          else pure [path | takeExtension path == ".hs"]) (sort entries)

-- | The names declared in the library at a given git ref, or in the working
-- tree when the ref is 'Nothing'.
namesAt :: Maybe String -> IO (Set.Set String)
namesAt Nothing = do
  files <- haskellFiles srcRoot
  Set.fromList . concat <$> traverse (fmap (map snd . declarationsOf . lines) . readFile') files
namesAt (Just ref) = do
  (code, out, _) <- readProcessWithExitCode "git"
    ["ls-tree", "-r", "--name-only", ref, "--", srcRoot] ""
  if code /= ExitSuccess
    then pure Set.empty
    else do
      let files = filter ((== ".hs") . takeExtension) (lines out)
      fmap (Set.fromList . concat) $ traverse (\file -> do
        contents <- readProcess "git" ["show", ref ++ ":" ++ file] ""
        pure (map snd (declarationsOf (lines contents)))) files

-- | Whether a git ref exists.
refExists :: String -> IO Bool
refExists ref = do
  (code, _, _) <- readProcessWithExitCode "git" ["rev-parse", "--verify", ref ++ "^{commit}"] ""
  pure (code == ExitSuccess)

-- * Modes

-- | Print @entity<TAB>version@ for every entity of the working tree.
resolve :: IO ()
resolve = do
  versions <- resolveVersions
  forM_ (Map.toAscList versions) $ \(name, version) ->
    putStrLn (name ++ "\t" ++ version)

-- | Report every exported entity whose haddock carries no @\@since@.
check :: IO ()
check = do
  files <- haskellFiles srcRoot
  missing <- fmap concat $ traverse (\file -> do
    ls <- lines <$> readFile' file
    let exports = exportsOf ls
        annotated = sinceAnnotated ls
        decls = declarationsOf ls
        -- A pattern synonym declares its name twice, on its signature and on
        -- its definition. Either carrying the annotation is enough.
        covered = Set.fromList [n | (l, n) <- decls, l `Set.member` annotated]
    pure
      [ Entity name file line
      | (line, name) <- decls
      , isExported exports name
      , not (line `Set.member` annotated)
      , not (name `Set.member` covered)
      ]) (filter (not . isUndocumentedModule) files)
  forM_ missing $ \e ->
    putStrLn (entityModule e ++ ":" ++ show (entityLine e) ++ ": no @since for " ++ entityName e)
  unless (null missing) $ do
    putStrLn (show (length missing) ++ " exported entities without @since")
    exitFailure

-- | The lines whose immediately preceding haddock block carries an @\@since@.
sinceAnnotated :: [String] -> Set.Set Int
sinceAnnotated ls = Set.fromList (go 1 ls Nothing)
  where
    go _ [] _ = []
    go i (l : rest) lastSince
      | isComment l =
          go (i + 1) rest (if hasSince l then Just i else lastSince)
      | isPragma l = go (i + 1) rest lastSince
      | all isSpace l = go (i + 1) rest Nothing
      | otherwise = case lastSince of
          -- The block applies to this declaration and to no later one.
          Just _  -> i : go (i + 1) rest Nothing
          Nothing -> go (i + 1) rest Nothing
    isComment l = "--" `isPrefixOf` dropWhile isSpace l
    isPragma l = "{-#" `isPrefixOf` dropWhile isSpace l
    hasSince = isInfixOf "@since"

-- | Insert @\@since@ into the haddock of every exported entity that has one
-- and lacks the annotation. An entity with no haddock block of its own is
-- reported instead, since there is nothing to annotate.
apply :: IO ()
apply = do
  versions <- resolveVersions
  files <- haskellFiles srcRoot
  undocumented <- fmap concat $ traverse (\file -> do
    ls <- lines <$> readFile' file
    let exports = exportsOf ls
        annotated = sinceAnnotated ls
        decls = declarationsOf ls
        covered = Set.fromList [n | (l, n) <- decls, l `Set.member` annotated]
        -- The first name declared on each line, so that neither the version
        -- nor the report re-scans the file per target.
        nameOfLine = Map.fromListWith (\_new old -> old) decls
        targets = Set.fromList
          [ line
          | (line, name) <- decls
          , isExported exports name
          , not (line `Set.member` annotated)
          , not (name `Set.member` covered)
          ]
        versionAt line = fromMaybe unreleasedVersion $ do
          name <- Map.lookup line nameOfLine
          Map.lookup name versions
        step (out, missing) line =
          case insertSince (versionAt line) line out of
            Just out' -> (out', missing)
            Nothing   ->
              let name = Map.findWithDefault "?" line nameOfLine
               in (out, Entity name file line : missing)
        -- Descending, so that an insertion never shifts a line still to come.
        (ls', missed) = foldl' step (ls, []) (Set.toDescList targets)
    unless (ls' == ls) $ writeFile file (unlines ls')
    pure missed) (filter (not . isUndocumentedModule) files)
  forM_ undocumented $ \e ->
    hPutStrLn stderr
      (entityModule e ++ ":" ++ show (entityLine e) ++ ": no haddock to annotate ("
         ++ entityName e ++ ")")
  putStrLn (show (length undocumented) ++ " entities have no haddock of their own")

-- | Insert @-- @since v@ at the end of the haddock block attached to the
-- declaration on the given line. 'Nothing' when the declaration has none.
insertSince :: String -> Int -> [String] -> Maybe [String]
insertSince version line ls = do
  let before = take (line - 1) ls
      after  = drop (line - 1) ls
      (upToDoc, pragmas) = breakEnd isPragma before
      (above, doc)       = breakEnd isComment upToDoc
  case doc of
    [] -> Nothing
    -- A block may open with a section heading before the doc comment proper.
    _ | not (any isHaddockStart doc) -> Nothing
    (first : _) ->
      let indent = takeWhile isSpace first
       in Just (above ++ doc ++ [indent ++ "--", indent ++ "-- @since " ++ version]
                  ++ pragmas ++ after)
  where
    isPragma l = "{-#" `isPrefixOf` dropWhile isSpace l
    isComment l = "--" `isPrefixOf` dropWhile isSpace l
    isHaddockStart l =
      let s = dropWhile isSpace l
       in "-- |" `isPrefixOf` s || "-- ^" `isPrefixOf` s

-- | Split off the longest suffix whose elements satisfy a predicate, as
-- @(everything before, that suffix)@.
breakEnd :: (a -> Bool) -> [a] -> ([a], [a])
breakEnd p xs =
  let (suffix, prefix) = span p (reverse xs)
   in (reverse prefix, reverse suffix)

-- | The resolved version of every entity of the working tree.
resolveVersions :: IO (Map.Map String String)
resolveVersions = do
  perRelease <- traverse resolveRelease releases
  current <- namesAt Nothing
  pure $ Map.fromList
    [ (name, firstSeen perRelease name) | name <- Set.toList current ]
  where
    resolveRelease (version, ref) = do
      ok <- refExists ref
      unless ok $
        hPutStrLn stderr ("no such ref, skipping: " ++ ref ++ " (" ++ version ++ ")")
      names <- if ok then namesAt (Just ref) else pure Set.empty
      pure (version, names)

    firstSeen perRelease name =
      fromMaybe unreleasedVersion $
        listToMaybe [v | (v, names) <- perRelease, name `Set.member` names]

main :: IO ()
main = getArgs >>= \case
  ["resolve"] -> resolve
  ["apply"]   -> apply
  ["check"]   -> check
  _           -> do
    putStrLn "usage: scripts/since.hs (resolve | apply | check)"
    exitWith (ExitFailure 2)
