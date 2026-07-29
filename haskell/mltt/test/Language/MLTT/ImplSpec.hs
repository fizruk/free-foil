{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.MLTT.ImplSpec (spec) where

import           Control.Monad                (forM_)
import qualified Control.Monad.Foil           as Foil
import           Data.Either                  (isLeft)
import           Data.String                  (fromString)
import           Language.MLTT.Eval
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Typecheck
import           Test.Hspec

-- | Parse a closed term and desugar it, which is what the interpreter does.
term :: String -> Term Foil.VoidS
term = desugar . fromString

spec :: Spec
spec = do
  describe "type checking" $ do
    it "accepts the polymorphic identity" $
      check emptyCtx (term "λ A . λ x . x") (term "Π (A : 𝕌) → A → A")
        `shouldBe` Right ()

    it "accepts a Σ-type destructured by a pattern binder" $
      check emptyCtx (term "λ (A, x) . x") (term "Π (p : Σ (A : 𝕌) × A) → π₁ p")
        `shouldBe` Right ()

    it "accepts a wildcard where the Π-type binds a variable" $
      check emptyCtx (term "λ _ . tt") (term "Π (A : 𝕌) → 𝟙")
        `shouldBe` Right ()

    it "infers a dependent projection" $
      fmap show (infer emptyCtx (term "π₂ (𝟙, tt)"))
        `shouldBe` Right "𝟙"

    it "rejects an argument of the wrong type" $
      check emptyCtx (term "(λ x . x : 𝟙 → 𝟙) 𝕌") (term "𝟙")
        `shouldSatisfy` isLeft

    it "rejects a λ against a non-Π type" $
      check emptyCtx (term "λ x . x") (term "𝟙")
        `shouldSatisfy` isLeft

    it "refuses to infer a type for a bare λ" $
      infer emptyCtx (term "λ x . x")
        `shouldSatisfy` isLeft

  describe "conversion" $ do
    it "sees through β-reduction" $
      conv Foil.emptyScope emptyDefs (term "(λ x . x) tt") (term "tt")
        `shouldBe` True

    it "is up to renaming of bound variables" $
      conv Foil.emptyScope emptyDefs (term "λ x . x") (term "λ y . y")
        `shouldBe` True

    it "distinguishes different normal forms" $
      conv Foil.emptyScope emptyDefs (term "λ x . x") (term "λ x . tt")
        `shouldBe` False

  describe "the example programs" $
    forM_ ["examples/core.mltt"] $ \path ->
      it (path <> " is accepted in full") $ do
        input <- readFile path
        case interpret input of
          Left err -> expectationFailure ("parse error: " <> err)
          Right results -> do
            forM_ results $ \result -> case result of
              Failed err -> expectationFailure err
              _          -> return ()
            results `shouldSatisfy` (not . null)
