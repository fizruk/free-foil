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

-- | Most of what fails here fails because the instances of the patterns are
-- generic: 'Control.Monad.Foil.withPattern' goes through an unordered set
-- of binders ('genericPatternOrder'), and 'Control.Monad.Foil.coSinkabilityProof'
-- through 'Control.Monad.Foil.SinkableK' ('genericCoSinkableCrash').
spec :: Spec
spec = do
  describe "CoSinkable FoilPattern" $
    coSinkableSpec foilPatternNames genFoilPattern $ \_ -> \case
      WithPatternOrder -> genericPatternOrder
      _                -> genericCoSinkableCrash
  describe "UnifiablePattern FoilPattern" $
    unifyPatternsSpec foilPatternNames genFoilPatternPair mergedBinderRenamings
  describe "α-equivalence" $ alphaSpec termSyntax $ \case
    AlphaEquivRefreshedAgrees -> genericPatternOrder
    _                         -> mergedBinderRenamings
  describe "relative monad" $ relMonadSpec termSyntax $ \name kinds -> case (name, kinds) of
    (SubstLeftUnit, _)  -> Holds
    (RbindLeftUnit, _)  -> Holds
    -- 'substitute' shortcuts the empty substitution and returns the term
    -- as it stands.
    (SubstRightUnit, _) -> Holds
    -- Both sides go through the same generic traversal, so they agree with
    -- each other, except where 'substitute' shortcuts an empty substitution.
    (SubstituteAgreesWithRbind, Just (Beta, _)) -> Holds
    _ -> genericPatternOrder
  describe "functor" $ functorSpec termSyntax (\_ _ -> genericSinkableCrash) $ \_ -> \case
    SinkAgreesWithLiftRM -> genericSinkableCrash
    _                    -> genericPatternOrder
