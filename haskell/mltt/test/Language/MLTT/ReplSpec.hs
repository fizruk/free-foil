{-# LANGUAGE OverloadedStrings #-}

-- | The interactive session: one stripe, allocated incrementally, with the
-- environment carried from step to step.
module Language.MLTT.ReplSpec (spec) where

import           Test.Hspec

import           Language.MLTT.Impl

spec :: Spec
spec = describe "an interactive session" $ do
  it "carries the environment from step to step, in one stripe" $ do
    let s0 = beginRepl (stripeRange (StripeIndex 0)) emptyEnv
        (s1, r1) = replStep "def one : 𝟙 := tt" s0
        (s2, r2) = replStep "compute one" s1
        (s3, r3) = replStep "def two : 𝟙 := one" s2
        (s4, r4) = replStep "def one : 𝟙 → 𝟙 := λ x ⇒ x" s3   -- a redefinition
        (s5, r5) = replStep "compute two" s4
        (_,  r6) = replStep "compute one tt" s5
    r1 `shouldBe` [Defined "one" []]
    r2 `shouldBe` [Computed "tt"]
    r3 `shouldBe` [Defined "two" []]
    r4 `shouldBe` [Defined "one" []]
    -- The old binding survives the rebinding of its spelling: `two` still
    -- reduces through it, while the spelling now means the new definition.
    r5 `shouldBe` [Computed "tt"]
    r6 `shouldBe` [Computed "tt"]

  it "accepts several declarations in one input" $ do
    let s0 = beginRepl (stripeRange (StripeIndex 0)) emptyEnv
        (_, rs) = replStep "def a : 𝟙 := tt\ndef b : 𝟙 := a\ncompute b" s0
    rs `shouldBe` [Defined "a" [], Defined "b" [], Computed "tt"]

  it "reports an input that does not parse, and the session survives" $ do
    let s0 = beginRepl (stripeRange (StripeIndex 0)) emptyEnv
        (s1, r1) = replStep "def broken :=" s0
        (_,  r2) = replStep "def a : 𝟙 := tt" s1
    map (take 11) [msg | Failed msg <- r1] `shouldBe` ["parse error"]
    r2 `shouldBe` [Defined "a" []]
