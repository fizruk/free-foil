{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.MLTT.ImplSpec (spec) where

import qualified Control.Monad.Foil           as Foil
import           Data.Either                  (isLeft)
import           Data.String                  (fromString)
import           Language.MLTT.Eval
import qualified Language.MLTT.Impl           as Impl
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Typecheck
import           Test.Hspec

-- | Parse a closed term and desugar it, which is what the interpreter does.
term :: String -> Term Foil.VoidS
term = desugar . fromString

-- | Interpret a program, reporting a parse error as a failed command.
run :: String -> [Impl.CommandResult]
run input = case Impl.interpret (SourceText input) of
  Left err      -> [Impl.Failed ("parse error: " <> err)]
  Right results -> results

-- | The messages of every command that was rejected.
failures :: [Impl.CommandResult] -> [String]
failures results = [err | Impl.Failed err <- results]

-- | The normal forms every @compute@ produced.
computed :: [Impl.CommandResult] -> [Impl.RenderedTerm]
computed results = [t | Impl.Computed t <- results]

spec :: Spec
spec = do
  describe "type checking" $ do
    it "accepts the polymorphic identity" $
      check emptyCtx (term "λ A ⇒ λ x ⇒ x") (term "Π (A : 𝕌) → A → A")
        `shouldBe` Right ()

    it "accepts a Σ-type destructured by a pattern binder" $
      check emptyCtx (term "λ (A, x) ⇒ x") (term "Π (p : Σ (A : 𝕌) × A) → π₁ p")
        `shouldBe` Right ()

    it "accepts a wildcard where the Π-type binds a variable" $
      check emptyCtx (term "λ _ ⇒ tt") (term "Π (A : 𝕌) → 𝟙")
        `shouldBe` Right ()

    it "infers a dependent projection" $
      fmap show (infer emptyCtx (term "π₂ (𝟙, tt)"))
        `shouldBe` Right "𝟙"

    it "rejects an argument of the wrong type" $
      check emptyCtx (term "(λ x ⇒ x : 𝟙 → 𝟙) 𝕌") (term "𝟙")
        `shouldSatisfy` isLeft

    it "rejects a λ against a non-Π type" $
      check emptyCtx (term "λ x ⇒ x") (term "𝟙")
        `shouldSatisfy` isLeft

    it "refuses to infer a type for a bare λ" $
      infer emptyCtx (term "λ x ⇒ x")
        `shouldSatisfy` isLeft

  describe "conversion" $ do
    it "sees through β-reduction" $
      conv Foil.emptyScope emptyDefs (term "(λ x ⇒ x) tt") (term "tt")
        `shouldBe` True

    it "is up to renaming of bound variables" $
      conv Foil.emptyScope emptyDefs (term "λ x ⇒ x") (term "λ y ⇒ y")
        `shouldBe` True

    it "distinguishes different normal forms" $
      conv Foil.emptyScope emptyDefs (term "λ x ⇒ x") (term "λ x ⇒ tt")
        `shouldBe` False

  -- A definition keeps the binder names it was elaborated with, while the same
  -- λ written under one more binder gets the next names. So in the programs
  -- below the two sides of a conversion name their pattern binders
  -- differently, and conversion has to pair the binders by position.
  describe "conversion of pattern binders" $ do
    it "does not accept refl fst2 as a proof that fst2 is the second projection" $
      -- Accepting it gave a closed coerce : 𝕌 that computes to tt.
      run (unlines
        [ "module Unsound"
        , "def fst2 : (𝕌 × 𝕌) → 𝕌"
        , "  := λ (x, y) ⇒ x"
        , "def bad : Π (z : 𝟙) → Id ((𝕌 × 𝕌) → 𝕌, fst2, λ (x, y) ⇒ y)"
        , "  := λ z ⇒ refl (fst2)"
        , "def coerce : 𝕌"
        , "  := J (λ f ⇒ λ q ⇒ f (𝟙, 𝕌), tt, bad tt)"
        , "compute coerce" ])
        `shouldSatisfy` \results ->
          Impl.Defined "bad" [] `notElem` results && null (computed results)

    it "accepts refl fst2 and refl snd2 as proofs about the projections they are" $
      failures (run (unlines
        [ "module Complete"
        , "def fst2 : (𝕌 × 𝕌) → 𝕌"
        , "  := λ (x, y) ⇒ x"
        , "def snd2 : (𝕌 × 𝕌) → 𝕌"
        , "  := λ (x, y) ⇒ y"
        , "check (λ z ⇒ refl (fst2)) : Π (z : 𝟙) → Id ((𝕌 × 𝕌) → 𝕌, fst2, λ (x, y) ⇒ x)"
        , "check (λ z ⇒ refl (snd2)) : Π (z : 𝟙) → Id ((𝕌 × 𝕌) → 𝕌, snd2, λ (x, y) ⇒ y)" ]))
        `shouldBe` []

    it "tells apart λ (x, _) ⇒ x and λ (_, y) ⇒ y, which bind one name each" $
      -- No outer binder is needed: both patterns bind one name, x0, and only
      -- their shapes differ.
      run (unlines
        [ "module Shape"
        , "def p1 : (𝕌 × 𝕌) → 𝕌"
        , "  := λ (x, _) ⇒ x"
        , "check refl (p1) : Id ((𝕌 × 𝕌) → 𝕌, p1, λ (_, y) ⇒ y)"
        , "def coerce : 𝕌"
        , "  := J (λ f ⇒ λ q ⇒ f (𝟙, 𝕌), tt, (refl (p1) : Id ((𝕌 × 𝕌) → 𝕌, p1, λ (_, y) ⇒ y)))"
        , "compute coerce" ])
        `shouldSatisfy` \results ->
          null [t | Impl.Checked t _ <- results]
            && Impl.Defined "coerce" [] `notElem` results
            && null (computed results)

    it "accepts refl p1 as a proof that p1 is the first projection" $
      failures (run (unlines
        [ "module Shape"
        , "def p1 : (𝕌 × 𝕌) → 𝕌"
        , "  := λ (x, _) ⇒ x"
        , "check refl (p1) : Id ((𝕌 × 𝕌) → 𝕌, p1, λ (x, _) ⇒ x)" ]))
        `shouldBe` []
