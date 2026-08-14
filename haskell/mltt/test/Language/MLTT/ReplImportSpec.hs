{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Imports into an interactive session: resolution for modules the world
-- holds, artifact-chain loading for modules it does not, and the failure
-- modes (unknown module, missing artifact, stale chain).
module Language.MLTT.ReplImportSpec (spec) where

import qualified Control.Monad.Foil           as Foil
import           Data.List                    (isInfixOf)
import           System.Directory             (getTemporaryDirectory,
                                               removePathForcibly)
import           System.FilePath              ((</>))
import           Test.Hspec

import           Language.MLTT.Build
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText, parseProgram,
                                               sourceLines)
import qualified Language.MLTT.Syntax.Abs     as Raw

srcP, srcP', srcQ, srcR :: SourceText
srcP  = sourceLines ["module P", "def base : 𝟙 := tt"]
srcP' = sourceLines ["module P", "def base : 𝟙 → 𝟙 := λ x ⇒ x"]
srcQ  = sourceLines ["module Q", "import P", "def q : 𝟙 := base"]
srcR  = sourceLines ["module R", "import Q", "def r : 𝟙 := q"]

modsOf :: [SourceText] -> [Raw.Module]
modsOf srcs =
  either error id . resolveUnits $
    concat [units | Right (Raw.AProgram _ units) <- map parseProgram srcs]

-- | A session over an empty world, on a stripe clear of the cached ones.
bareSession :: Repl Foil.VoidS
bareSession = beginRepl (stripeRange (StripeIndex 9)) emptyEnv

failures :: [CommandResult] -> [ErrorMessage]
failures results = [msg | Failed msg <- results]

spec :: Spec
spec = describe "importing into a session" $ do
  it "loads a cached chain, and brings only the imported module's exports in" $ do
    dir <- (</> "mltt-repl-import-cache") <$> getTemporaryDirectory
    removePathForcibly dir
    _ <- buildModules Sequential (Just dir) (modsOf [srcP, srcQ, srcR])
    (s1, r1) <- replImport (Just dir) (Raw.VarIdent "R") bareSession
    r1 `shouldBe` [ LoadedModule "P", LoadedModule "Q", LoadedModule "R"
                  , Imported "R" ]
    let (s2, r2) = replStep "compute r" s1
    r2 `shouldBe` [Computed "tt"]
    -- Q's q reduces through r, but only R's exports can be named.
    let (s3, r3) = replStep "compute q" s2
    failures r3 `shouldSatisfy` (not . null)
    -- A further import is resolution only: Q is in the world now.
    (s4, r4) <- replImport (Just dir) (Raw.VarIdent "Q") s3
    r4 `shouldBe` [Imported "Q"]
    let (_, r5) = replStep "compute q" s4
    r5 `shouldBe` [Computed "tt"]

  it "refuses an unknown module, naming the artifact it looked for" $ do
    (_, r1) <- replImport Nothing (Raw.VarIdent "M") bareSession
    failures r1 `shouldSatisfy` (not . null)
    dir <- (</> "mltt-repl-import-empty") <$> getTemporaryDirectory
    removePathForcibly dir
    (_, r2) <- replImport (Just dir) (Raw.VarIdent "M") bareSession
    concat (failures r2) `shouldSatisfy` ("M.mltta" `isInfixOf`)

  it "rejects a stale chain instead of loading it" $ do
    dir <- (</> "mltt-repl-import-stale") <$> getTemporaryDirectory
    removePathForcibly dir
    _ <- buildModules Sequential (Just dir) (modsOf [srcP, srcQ])
    -- P changes and is rebuilt alone, so Q's artifact records a hash the
    -- cache no longer agrees with.
    _ <- buildModules Sequential (Just dir) (modsOf [srcP'])
    (_, r) <- replImport (Just dir) (Raw.VarIdent "Q") bareSession
    concat (failures r) `shouldSatisfy` ("stale" `isInfixOf`)
