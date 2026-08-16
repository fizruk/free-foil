{-# LANGUAGE OverloadedStrings #-}
-- | Multi-binder sugar.
--
-- @λ a b c ⇒ e@ and @Π (a b c : T) → B@ are parse-time sugar for the nested
-- forms: the grammar's @define@ rules construct nested nodes, so the abstract
-- syntax never records which spelling was written. The property under test is
-- exactly that indistinguishability.
module Language.MLTT.SugarSpec (spec) where

import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated (SourceText (..))
import           Test.Hspec

-- | Interpret a program, reporting a parse error as a failed command.
run :: String -> [CommandResult]
run input = case interpret (SourceText input) of
  Left err      -> [Failed ("parse error: " <> err)]
  Right results -> results

-- | The messages of every command that was rejected.
failures :: [CommandResult] -> [String]
failures results = [err | Failed err <- results]

-- | The normal forms every @compute@ produced.
computed :: [CommandResult] -> [RenderedTerm]
computed results = [term | Computed term <- results]

-- | A module around the given lines.
inModule :: [String] -> String
inModule ls = unlines ("module M" : ls)

spec :: Spec
spec = do
  describe "multi-binder λ" $ do
    it "means the nested λs, and nothing downstream can tell" $
      computed (run (inModule
        ["compute (λ a b ⇒ a : 𝟙 → 𝟙 → 𝟙)"]))
        `shouldBe`
      computed (run (inModule
        ["compute (λ a ⇒ λ b ⇒ a : 𝟙 → 𝟙 → 𝟙)"]))

    it "takes any number of binders" $
      failures (run (inModule
        [ "def pick : 𝟙 → 𝟙 → 𝟙 → 𝟙 → 𝟙 → 𝟙"
        , "  := λ a b c d e ⇒ c" ]))
        `shouldBe` []

    it "admits any pattern in any position" $
      failures (run (inModule
        [ "def first : (𝟙 × 𝟙) → 𝟙 → 𝟙"
        , "  := λ (a, b) c ⇒ a" ]))
        `shouldBe` []

  describe "a Π group" $ do
    it "means the nested Πs with the type repeated at each binder" $
      failures (run (inModule
        [ "def diag : Π (x y z : 𝕌) → 𝕌 := λ x y z ⇒ y"
        , "check diag : Π (x : 𝕌) → Π (y : 𝕌) → Π (z : 𝕌) → 𝕌" ]))
        `shouldBe` []

    it "takes up to four binders" $
      failures (run (inModule
        ["check (λ a b c d ⇒ tt : Π (a b c d : 𝟙) → 𝟙) : Π (a b c d : 𝟙) → 𝟙"]))
        `shouldBe` []

    it "may bind dependently within the group" $
      -- The later binders of a group are in scope of the repeated type only,
      -- but the body sees them all in order.
      failures (run (inModule
        ["check (λ A B f x ⇒ f x : Π (A B : 𝕌) → (A → B) → A → B)"
          <> " : Π (A : 𝕌) → Π (B : 𝕌) → (A → B) → A → B"]))
        `shouldBe` []
