{-# LANGUAGE OverloadedStrings #-}

-- | Separate checking and linking, on the diamond: a shared import @I@, two
-- independent modules @A@ and @B@ over it, and a client @C@ of both.
--
-- What is under test is the whole point of the stripe layout: that @A@ and
-- @B@ can be checked with no knowledge of each other — in either order, or
-- in parallel — and linked afterwards at the cost of a range comparison,
-- with the shared import identified rather than renamed apart.
module Language.MLTT.LinkSpec (spec) where

import           Control.Monad.Foil.Registry (StripeIndex (..))
import           Control.Concurrent           (forkIO, newEmptyMVar, putMVar,
                                               takeMVar)
import           Control.Exception            (evaluate)
import qualified Control.Monad.Foil           as Foil
import qualified Control.Monad.Foil.Blocks    as Blocks
import           Data.Either                  (isLeft)
import qualified Data.Map                     as Map
import           Data.Maybe                   (isJust, isNothing)
import           Test.Hspec

import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText,
                                               parseProgram, sourceLines)
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Typecheck      (ctxScope)

srcI, srcA, srcB, srcC, srcX :: SourceText
srcI = sourceLines ["module I", "def base : 𝟙 := tt"]
srcA = sourceLines ["module A", "import I", "def a : 𝟙 := base"]
srcB = sourceLines ["module B", "import I", "def b : 𝟙 → 𝟙 := λ x ⇒ base"]
srcC = sourceLines ["module C", "import A", "import B", "compute b a"]
srcX = sourceLines ["module X", "def unrelated : 𝟙 := tt"]

oneModule :: SourceText -> Raw.Module
oneModule src = case parseProgram src of
  Right (Raw.AProgram _ [Raw.UnitModule _ m]) -> m
  Right _                    -> error "expected exactly one module"
  Left err                   -> error err

mI, mA, mB, mC, mX :: Raw.Module
mI = oneModule srcI
mA = oneModule srcA
mB = oneModule srcB
mC = oneModule srcC
mX = oneModule srcX


-- Two chains over a shared base: P; Q imports P; R imports Q; S imports P;
-- T imports S; U imports both chain ends.
srcP, srcQ, srcR, srcS, srcT, srcU :: SourceText
srcP = sourceLines ["module P", "def base : \120793 := tt"]
srcQ = sourceLines ["module Q", "import P", "def q : \120793 := base"]
srcR = sourceLines ["module R", "import Q", "def r : \120793 := q"]
srcS = sourceLines
  [ "module S (A : \120140) (a : A)"
  , "import P"
  , "def s : A \8594 A := \955 u \8658 a"
  , "def sbase : \120793 := base"
  ]
srcT = sourceLines ["module T", "import S", "def t : \120793 \8594 \120793 := s \120793 sbase"]
srcU = sourceLines ["module U", "import R", "import T", "compute t r"]

mP, mQ, mR, mS, mT, mU :: Raw.Module
mP = oneModule srcP
mQ = oneModule srcQ
mR = oneModule srcR
mS = oneModule srcS
mT = oneModule srcT
mU = oneModule srcU

-- | The registry as the sequential driver would build it, so that the linked
-- run and 'interpretModules' hand out the same stripes.
registry :: Registry
registry = Map.fromList
  [ (moduleName mI, StripeIndex 0), (moduleName mA, StripeIndex 1)
  , (moduleName mB, StripeIndex 2) ]

-- | The raw name of everything a checked module can refer to, by spelling.
declaredIds :: CheckedModule c -> [(Raw.VarIdent, Int)]
declaredIds cm = withCheckedModule cm $ \_ env _ ->
  Map.toList (fmap Foil.nameId (envDeclared env))

-- | Check @I@, then @A@ and @B@ independently against it, link, and check
-- @C@ in the linked environment. The flag swaps the link order.
linkedRun :: Bool -> Either String [CommandResult]
linkedRun swapped =
  withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mI) $ \_ envI resultsI ->
    let ca = checkModule (stripeRange (StripeIndex 1)) envI mA
        cb = checkModule (stripeRange (StripeIndex 2)) envI mB
        runC envK = goModules registry envK [mC]
        linked
          | swapped   = linkModules cb ca runC
          | otherwise = linkModules ca cb runC
     in fmap (\resultsC -> resultsI <> resultsOf ca <> resultsOf cb <> resultsC) linked

spec :: Spec
spec = do
  describe "separate checking and linking" $ do
    it "matches the sequential interpreter" $
      linkedRun False `shouldBe` Right (interpretModules [mI, mA, mB, mC])

    it "matches it with the link order swapped" $
      linkedRun True `shouldBe` Right (interpretModules [mI, mA, mB, mC])

    it "computes through both sides of the diamond" $
      fmap (\rs -> [t | Computed t <- rs]) (linkedRun False) `shouldBe` Right ["tt"]

  describe "determinism of declaration names" $ do
    it "numbers a stripe's declarations from its base, in order" $
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mI) $ \_ envI _ ->
        declaredIds (checkModule (stripeRange (StripeIndex 1)) envI mA) `shouldBe`
          [ (Raw.VarIdent "a", Foil.nameRangeLo (stripeRange (StripeIndex 1)))
          , (Raw.VarIdent "base", Foil.nameRangeLo (stripeRange (StripeIndex 0)))
          ]

    it "gives a module the same names whatever else was checked before" $
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mI) $ \_ envI _ ->
        withCheckedModule (checkModule (stripeRange (StripeIndex 3)) envI mX) $ \_ envX _ ->
          declaredIds (checkModule (stripeRange (StripeIndex 1)) envX mA)
            `shouldBe` declaredIds (checkModule (stripeRange (StripeIndex 1)) envI mA)


  describe "linking chains" $
    it "folds each chain into one unit, then links, matching the sequential run" $
      -- The chains get interleaved stripes (Q = 1, S = 2, R = 3, T = 4), so
      -- the convex hulls of the two chains overlap while their reservations
      -- do not: the case that forces evidence over a set of ranges.
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mP) $ \_ envP resultsP ->
        let chainQR = checkModuleAfter (stripeRange (StripeIndex 3)) (checkModule (stripeRange (StripeIndex 1)) envP mQ) mR
            chainST = checkModuleAfter (stripeRange (StripeIndex 4)) (checkModule (stripeRange (StripeIndex 2)) envP mS) mT
            chainRegistry = Map.fromList
              [ (moduleName mP, StripeIndex 0), (moduleName mQ, StripeIndex 1)
              , (moduleName mS, StripeIndex 2), (moduleName mR, StripeIndex 3)
              , (moduleName mT, StripeIndex 4) ]
            linked = linkModules chainQR chainST (\envU -> goModules chainRegistry envU [mU])
         in fmap (\resultsU -> resultsP <> resultsOf chainQR <> resultsOf chainST <> resultsU) linked
              `shouldBe` Right (interpretModules [mP, mQ, mR, mS, mT, mU])

  describe "checking on separate threads" $
    it "checks the two chains concurrently and matches the sequential run" $
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mP) $ \_ envP resultsP -> do
        vQR <- newEmptyMVar
        vST <- newEmptyMVar
        _ <- forkIO $ do
          let chain = checkModuleAfter (stripeRange (StripeIndex 3))
                        (checkModule (stripeRange (StripeIndex 1)) envP mQ) mR
          _ <- evaluate (length (show (resultsOf chain)))  -- do the work here
          putMVar vQR chain
        _ <- forkIO $ do
          let chain = checkModuleAfter (stripeRange (StripeIndex 4))
                        (checkModule (stripeRange (StripeIndex 2)) envP mS) mT
          _ <- evaluate (length (show (resultsOf chain)))
          putMVar vST chain
        chainQR <- takeMVar vQR
        chainST <- takeMVar vST
        let chainRegistry = Map.fromList
              [ (moduleName mP, StripeIndex 0), (moduleName mQ, StripeIndex 1)
              , (moduleName mS, StripeIndex 2), (moduleName mR, StripeIndex 3)
              , (moduleName mT, StripeIndex 4) ]
        case linkModules chainQR chainST (\envU -> goModules chainRegistry envU [mU]) of
          Left err -> expectationFailure err
          Right resultsU ->
            (resultsP <> resultsOf chainQR <> resultsOf chainST <> resultsU)
              `shouldBe` interpretModules [mP, mQ, mR, mS, mT, mU]

  describe "linking failures" $
    it "refuses two modules whose stripes overlap" $
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mI) $ \_ envI _ ->
        let ca  = checkModule (stripeRange (StripeIndex 1)) envI mA
            cb' = checkModule (stripeRange (StripeIndex 1)) envI mB  -- a registry gone wrong
         in linkModules ca cb' (\_ -> ())
              `shouldSatisfy` isLeft

  describe "re-attachment by inclusion (checkExtScope)" $
    it "accepts each side against the union, and not the other way around" $
      withCheckedModule (checkModule (stripeRange (StripeIndex 0)) emptyEnv mI) $ \_ envI _ ->
        let ca = checkModule (stripeRange (StripeIndex 1)) envI mA
            cb = checkModule (stripeRange (StripeIndex 2)) envI mB
         in withCheckedModule ca $ \_ envA _ ->
              linkModules ca cb (\envK ->
                ( isJust (Blocks.checkExtScope (ctxScope (envCtx envA)) (ctxScope (envCtx envK)))
                , isNothing (Blocks.checkExtScope (ctxScope (envCtx envK)) (ctxScope (envCtx envA)))
                ))
                `shouldBe` Right (True, True)
