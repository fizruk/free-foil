{-# LANGUAGE OverloadedStrings #-}

-- | Separate checking and linking, on the diamond: a shared import @I@, two
-- independent modules @A@ and @B@ over it, and a client @C@ of both.
--
-- What is under test is the whole point of the stripe layout: that @A@ and
-- @B@ can be checked with no knowledge of each other — in either order, or
-- in parallel — and linked afterwards at the cost of a range comparison,
-- with the shared import identified rather than renamed apart.
module Language.MLTT.LinkSpec (spec) where

import qualified Control.Monad.Foil           as Foil
import qualified Control.Monad.Foil.Blocks    as Blocks
import           Data.Either                  (isLeft)
import qualified Data.Map                     as Map
import           Data.Maybe                   (isJust, isNothing)
import           Test.Hspec

import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (parseProgram)
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Typecheck      (ctxScope)

srcI, srcA, srcB, srcC, srcX :: String
srcI = unlines ["module I", "def base : 𝟙 := tt"]
srcA = unlines ["module A", "import I", "def a : 𝟙 := base"]
srcB = unlines ["module B", "import I", "def b : 𝟙 → 𝟙 := λ x ⇒ base"]
srcC = unlines ["module C", "import A", "import B", "compute b a"]
srcX = unlines ["module X", "def unrelated : 𝟙 := tt"]

oneModule :: String -> Raw.Module
oneModule src = case parseProgram src of
  Right (Raw.AProgram _ [m]) -> m
  Right _                    -> error "expected exactly one module"
  Left err                   -> error err

mI, mA, mB, mC, mX :: Raw.Module
mI = oneModule srcI
mA = oneModule srcA
mB = oneModule srcB
mC = oneModule srcC
mX = oneModule srcX

-- | The registry as the sequential driver would build it, so that the linked
-- run and 'interpretModules' hand out the same stripes.
registry :: Registry
registry = Map.fromList
  [ (moduleName mI, 0), (moduleName mA, 1), (moduleName mB, 2) ]

-- | The results a checked module reported.
resultsOf :: CheckedModule c -> [CommandResult]
resultsOf cm = withCheckedModule cm (\_ _ rs -> rs)

-- | The raw name of everything a checked module can refer to, by spelling.
declaredIds :: CheckedModule c -> [(Raw.VarIdent, Int)]
declaredIds cm = withCheckedModule cm $ \_ env _ ->
  Map.toList (fmap Foil.nameId (envDeclared env))

-- | Check @I@, then @A@ and @B@ independently against it, link, and check
-- @C@ in the linked environment. The flag swaps the link order.
linkedRun :: Bool -> Either String [CommandResult]
linkedRun swapped =
  withCheckedModule (checkModule (stripeRange 0) emptyEnv mI) $ \_ envI resultsI ->
    let ca = checkModule (stripeRange 1) envI mA
        cb = checkModule (stripeRange 2) envI mB
        runC envK = goModules registry envK [mC]
        linked
          | swapped   = linkModules (moduleName mB) cb (moduleName mA) ca runC
          | otherwise = linkModules (moduleName mA) ca (moduleName mB) cb runC
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
      withCheckedModule (checkModule (stripeRange 0) emptyEnv mI) $ \_ envI _ ->
        declaredIds (checkModule (stripeRange 1) envI mA) `shouldBe`
          [ (Raw.VarIdent "a", firstStripeBase + stripeSize)
          , (Raw.VarIdent "base", firstStripeBase)
          ]

    it "gives a module the same names whatever else was checked before" $
      withCheckedModule (checkModule (stripeRange 0) emptyEnv mI) $ \_ envI _ ->
        withCheckedModule (checkModule (stripeRange 3) envI mX) $ \_ envX _ ->
          declaredIds (checkModule (stripeRange 1) envX mA)
            `shouldBe` declaredIds (checkModule (stripeRange 1) envI mA)

  describe "linking failures" $
    it "refuses two modules whose stripes overlap" $
      withCheckedModule (checkModule (stripeRange 0) emptyEnv mI) $ \_ envI _ ->
        let ca  = checkModule (stripeRange 1) envI mA
            cb' = checkModule (stripeRange 1) envI mB  -- a registry gone wrong
         in linkModules (moduleName mA) ca (moduleName mB) cb' (\_ -> ())
              `shouldSatisfy` isLeft

  describe "re-attachment by inclusion (checkExtScope)" $
    it "accepts each side against the union, and not the other way around" $
      withCheckedModule (checkModule (stripeRange 0) emptyEnv mI) $ \_ envI _ ->
        let ca = checkModule (stripeRange 1) envI mA
            cb = checkModule (stripeRange 2) envI mB
         in withCheckedModule ca $ \_ envA _ ->
              linkModules (moduleName mA) ca (moduleName mB) cb (\envK ->
                ( isJust (Blocks.checkExtScope (ctxScope (envCtx envA)) (ctxScope (envCtx envK)))
                , isNothing (Blocks.checkExtScope (ctxScope (envCtx envK)) (ctxScope (envCtx envA)))
                ))
                `shouldBe` Right (True, True)
