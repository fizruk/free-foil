{-# LANGUAGE LambdaCase #-}
-- | The laws of "Control.Monad.Foil.Laws" and "Control.Monad.Free.Foil.Laws"
-- for the λΠ-calculus of "Language.LambdaPi.Impl.FreeFoilTH" (a generated
-- signature, with patterns that are wildcards, variables and pairs, and
-- generically derived instances for them).
module Language.LambdaPi.Impl.FreeFoilTHLawsSpec (spec) where

import           Test.Hspec

import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Laws
import           Language.LambdaPi.Impl.LawsSyntax (foilPatternNames, genFoilPattern,
                                                    genFoilPatternPair, termSyntax)

-- | The instances of the patterns are generic, so this checks the generic
-- 'Control.Monad.Foil.withPattern' and 'Control.Monad.Foil.coSinkabilityProof',
-- and the default 'Control.Monad.Foil.unifyPatterns'. The pins are along
-- renamings that are not inclusions, outside the domain of the laws.
spec :: Spec
spec = do
  describe "CoSinkable FoilPattern" $
    coSinkableSpec foilPatternNames genFoilPattern extensionByCoercion
  describe "UnifiablePattern FoilPattern" $
    unifyPatternsSpec foilPatternNames genFoilPatternPair Holds
  describe "α-equivalence" $ alphaSpec termSyntax (const Holds)
  describe "relative monad" $ relMonadSpec termSyntax (\_ _ -> Holds)
  describe "functor" $ functorSpec termSyntax (\_ _ -> Holds) $ \cls -> \case
    SinkAgreesWithLiftRM -> sinkAgreesOnInclusions cls
    _                    -> Holds
