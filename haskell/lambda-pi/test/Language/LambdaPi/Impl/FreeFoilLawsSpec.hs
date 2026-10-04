{-# LANGUAGE LambdaCase #-}
-- | The laws of "Control.Monad.Free.Foil.Laws" for the λΠ-calculus of
-- "Language.LambdaPi.Impl.FreeFoil" (a hand-written signature, with one
-- 'Control.Monad.Foil.NameBinder' per scoped term).
module Language.LambdaPi.Impl.FreeFoilLawsSpec (spec) where

import           Test.Hspec

import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Laws
import           Language.LambdaPi.Impl.LawsSyntax (lambdaPiSyntax)

spec :: Spec
spec = do
  describe "α-equivalence" $ alphaSpec lambdaPiSyntax (const Holds)
  describe "relative monad" $ relMonadSpec lambdaPiSyntax (\_ _ -> Holds)
  describe "functor" $ functorSpec lambdaPiSyntax (\_ _ -> Holds) $ \cls -> \case
    SinkAgreesWithLiftRM -> sinkAgreesOnInclusions cls
    _                    -> Holds
