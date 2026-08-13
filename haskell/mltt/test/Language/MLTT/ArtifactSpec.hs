{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

-- | The serialisation round trip, on the diamond of chains from
-- "Language.MLTT.LinkSpec": check modules and write artifacts in one run,
-- then start from nothing, load the artifacts instead of the sources, link,
-- and check a client on top.
module Language.MLTT.ArtifactSpec (spec) where

import qualified Control.Monad.Foil           as Foil
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import           Test.Hspec

import           Language.MLTT.Artifact
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (parseProgram)
import qualified Language.MLTT.Syntax.Abs     as Raw

srcP, srcQ, srcR, srcS, srcT, srcU :: String
srcP = unlines ["module P", "def base : 𝟙 := tt"]
srcQ = unlines ["module Q", "import P", "def q : 𝟙 := base"]
srcR = unlines ["module R", "import Q", "def r : 𝟙 := q"]
srcS = unlines
  [ "module S (A : 𝕌) (a : A)"
  , "import P"
  , "def s : A → A := λ u ⇒ a"
  , "def sbase : 𝟙 := base"
  ]
srcT = unlines ["module T", "import S", "def t : 𝟙 → 𝟙 := s 𝟙 sbase"]
srcU = unlines ["module U", "import R", "import T", "compute t r"]

oneModule :: String -> Raw.Module
oneModule src = case parseProgram src of
  Right (Raw.AProgram _ [m]) -> m
  Right _                    -> error "expected exactly one module"
  Left err                   -> error err

mP, mQ, mR, mS, mT, mU :: Raw.Module
mP = oneModule srcP
mQ = oneModule srcQ
mR = oneModule srcR
mS = oneModule srcS
mT = oneModule srcT
mU = oneModule srcU

-- | Check modules sequentially (they are given in build order) and produce
-- an artifact for each, exactly as a caching driver would.
artifactsOf :: [Raw.Module] -> Map Raw.VarIdent ModuleArtifact
artifactsOf = go (0 :: Int) Map.empty emptyEnv
  where
    go :: Foil.Distinct n
       => Int -> Map Raw.VarIdent ModuleArtifact -> Env n -> [Raw.Module]
       -> Map Raw.VarIdent ModuleArtifact
    go _ acc _ [] = acc
    go i acc env (m : ms) =
      let importHashes =
            [ (x, artifactHash (acc Map.! x))
            | Raw.AnImport _ x <- moduleImports m ]
          cm = checkModule (stripeRange (StripeIndex i)) env m
          a  = makeArtifact (moduleName m) (StripeIndex i) importHashes cm
       in withCheckedModule cm $ \_ env' results ->
            if succeeded results
              then go (i + 1) (Map.insert (artifactModule a) a acc) env' ms
              else error ("module failed to check: " <> show results)

arts :: Map Raw.VarIdent ModuleArtifact
arts = artifactsOf [mP, mQ, mR, mS, mT]

art :: Raw.VarIdent -> ModuleArtifact
art m = arts Map.! m

hashesOf :: [Raw.VarIdent] -> Map Raw.VarIdent ContentHash
hashesOf ms = Map.fromList [(m, artifactHash (art m)) | m <- ms]

-- | The raw name of everything a checked module can refer to, by spelling.
declaredIds :: CheckedModule c -> [(Raw.VarIdent, Int)]
declaredIds cm = withCheckedModule cm $ \_ env _ ->
  Map.toList (fmap Foil.nameId (envDeclared env))

resultsOf :: CheckedModule c -> [CommandResult]
resultsOf cm = withCheckedModule cm (\_ _ rs -> rs)

spec :: Spec
spec = do
  describe "the wire format" $ do
    it "round-trips through render and read" $
      readArtifact (renderArtifact (art "S")) `shouldBe` Right (art "S")

    it "stores fully qualified spellings, not names" $
      map adSpelling (artifactDecls (art "S")) `shouldBe` ["s", "sbase"]

  describe "loading" $ do
    it "reconstructs the very names the check allocated" $
      case loadArtifact Map.empty (stripeRange (StripeIndex 0)) emptyEnv (art "P") of
        Left err  -> expectationFailure err
        Right cmP ->
          declaredIds cmP `shouldBe`
            declaredIds (checkModule (stripeRange (StripeIndex 0)) emptyEnv mP)

    it "a module checks against a loaded import exactly as against a checked one" $
      case loadArtifact Map.empty (stripeRange (StripeIndex 0)) emptyEnv (art "P") of
        Left err  -> expectationFailure err
        Right cmP ->
          withCheckedModule cmP $ \_ envP _ ->
            withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mP) $ \_ envP' _ -> do
              resultsOf (checkModule (stripeRange (StripeIndex 2)) envP mS)
                `shouldBe` resultsOf (checkModule (stripeRange (StripeIndex 2)) envP' mS)
              declaredIds (checkModule (stripeRange (StripeIndex 2)) envP mS)
                `shouldBe` declaredIds (checkModule (stripeRange (StripeIndex 2)) envP' mS)

    it "rejects a stale artifact instead of linking it" $
      case loadArtifact Map.empty (stripeRange (StripeIndex 0)) emptyEnv (art "P") of
        Left err  -> expectationFailure err
        Right cmP ->
          withCheckedModule cmP $ \_ envP _ ->
            case loadArtifact (Map.singleton "P" (ContentHash 0)) (stripeRange (StripeIndex 1)) envP (art "Q") of
              Left err -> err `shouldContain` "stale"
              Right _  -> expectationFailure "a stale artifact was accepted"

    it "loads at a moved stripe: the relocation case" $
      case loadArtifact Map.empty (stripeRange (StripeIndex 7)) emptyEnv (art "P") of
        Left err  -> expectationFailure err
        Right cmP -> do
          let Foil.NameRange lo _ = stripeRange (StripeIndex 7)
          map snd (declaredIds cmP) `shouldBe` [lo]
          withCheckedModule cmP $ \_ envP _ ->
            resultsOf (checkModule (stripeRange (StripeIndex 1)) envP mQ)
              `shouldBe` [EnteredModule "Q", Defined "q" []]

  describe "the full diamond from cache" $
    it "loads both chains, links them, and checks the client on top" $
      let run = do
            cmP <- loadArtifact Map.empty (stripeRange (StripeIndex 0)) emptyEnv (art "P")
            withCheckedModule cmP $ \_ envP _ -> do
              cmQ <- loadArtifact (hashesOf ["P"]) (stripeRange (StripeIndex 1)) envP (art "Q")
              chainQR <- loadArtifactAfter (hashesOf ["Q"]) (stripeRange (StripeIndex 3)) cmQ (art "R")
              cmS <- loadArtifact (hashesOf ["P"]) (stripeRange (StripeIndex 2)) envP (art "S")
              chainST <- loadArtifactAfter (hashesOf ["S"]) (stripeRange (StripeIndex 4)) cmS (art "T")
              let registry = Map.fromList
                    [ (moduleName mP, StripeIndex 0), (moduleName mQ, StripeIndex 1)
                    , (moduleName mS, StripeIndex 2), (moduleName mR, StripeIndex 3)
                    , (moduleName mT, StripeIndex 4) ]
              linkModules chainQR chainST $ \envU -> goModules registry envU [mU]
       in run `shouldBe` Right [EnteredModule "U", Computed "tt"]
