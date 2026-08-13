{-# LANGUAGE OverloadedStrings #-}

-- | The builder: three scheduling modes over one driver, and the on-disk
-- cache with content-defined staleness.
module Language.MLTT.BuildSpec (spec) where

import           System.Directory             (getTemporaryDirectory,
                                               removePathForcibly)
import           System.FilePath              ((</>))
import           Test.Hspec

import           Language.MLTT.Build
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText,
                                               parseProgram, sourceLines)
import qualified Language.MLTT.Syntax.Abs     as Raw

srcP, srcQ, srcQ', srcR, srcS, srcT, srcU :: SourceText
srcP = sourceLines ["module P", "def base : 𝟙 := tt"]
srcQ = sourceLines ["module Q", "import P", "def q : 𝟙 := base"]
srcQ' = srcQ <> sourceLines ["def q2 : 𝟙 := tt"]
srcR = sourceLines ["module R", "import Q", "def r : 𝟙 := q"]
srcS = sourceLines
  [ "module S (A : 𝕌) (a : A)"
  , "import P"
  , "def s : A → A := λ u ⇒ a"
  , "def sbase : 𝟙 := base"
  ]
srcT = sourceLines ["module T", "import S", "def t : 𝟙 → 𝟙 := s 𝟙 sbase"]
srcU = sourceLines ["module U", "import R", "import T", "compute t r"]

oneModule :: SourceText -> Raw.Module
oneModule src = case parseProgram src of
  Right (Raw.AProgram _ [m]) -> m
  Right _                    -> error "expected exactly one module"
  Left err                   -> error err

ms :: [Raw.Module]
ms = map oneModule [srcP, srcQ, srcR, srcS, srcT, srcU]

loadedNames :: [CommandResult] -> [RenderedName]
loadedNames results = [name | LoadedModule name <- results]

checkedNames :: [CommandResult] -> [RenderedName]
checkedNames results = [name | EnteredModule name <- results]

spec :: Spec
spec = do
  describe "three ways to build" $
    it "sequential, linked and parallel agree, and match the interpreter" $ do
      seqR <- buildModules Sequential Nothing ms
      lnkR <- buildModules Linked Nothing ms
      parR <- buildModules Parallel Nothing ms
      seqR `shouldBe` Right (interpretModules ms)
      lnkR `shouldBe` seqR
      parR `shouldBe` seqR

  describe "the cache" $
    it "loads the unchanged, rebuilds the stale, and cuts off early" $ do
      dir <- (</> "mltt-build-spec-cache") <$> getTemporaryDirectory
      removePathForcibly dir
      r1 <- buildModules Linked (Just dir) ms
      fmap loadedNames r1 `shouldBe` Right []
      -- A rebuild of the same sources loads everything; note that a cached
      -- module's compute commands are not re-run.
      r2 <- buildModules Linked (Just dir) ms
      fmap loadedNames r2 `shouldBe` Right ["P", "Q", "R", "S", "T", "U"]
      -- Adding a declaration to Q dirties Q, and R through its recorded
      -- import hash; but R's own declarations come out unchanged, so its
      -- content hash is the same and U is loaded: early cutoff.
      let ms' = [ if moduleName m == moduleName (oneModule srcQ)
                    then oneModule srcQ' else m
                | m <- ms ]
      r3 <- buildModules Linked (Just dir) ms'
      fmap checkedNames r3 `shouldBe` Right ["Q", "R"]
      fmap loadedNames r3 `shouldBe` Right ["P", "S", "T", "U"]

  describe "a session over a build" $
    it "starts seeing nothing; imports bring built modules' exports in" $ do
      r <- buildModulesWith Linked Nothing ms $ \registry env results -> do
        let s0 = sessionOver registry env
            (_, r0) = replStep "def nope : 𝟙 := t r" s0
        (s1, r1) <- replImport Nothing (Raw.VarIdent "T") s0
        (s2, r2) <- replImport Nothing (Raw.VarIdent "R") s1
        let (s3, r3) = replStep "def mine : 𝟙 := t r" s2
            (_,  r4) = replStep "compute mine" s3
        pure ( succeeded results, null [msg | Failed msg <- r0]
             , r1, r2, r3, r4 )
      r `shouldBe` Right ( True, False
                         , [Imported "T"], [Imported "R"]
                         , [Defined "mine" []], [Computed "tt"] )
