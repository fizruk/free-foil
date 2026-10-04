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
    coSinkableSpec foilPatternNames genFoilPattern $ \cls -> \case
      WithPatternOrder -> genericPatternOrder
      CoSinkExtension  -> genericCoSinkExtension cls
      _                -> genericCoSinkableCrash
  describe "UnifiablePattern FoilPattern" $
    unifyPatternsSpec foilPatternNames genFoilPatternPair mergedBinderRenamings
  describe "α-equivalence" $ alphaSpec termSyntax $ \case
    AlphaEquivRefreshedAgrees -> genericPatternOrder
    _                         -> mergedBinderRenamings
  describe "relative monad" $ relMonadSpec termSyntax $ \name kinds -> case (name, kinds) of
    (SubstLeftUnit, _)  -> Holds
    (RbindLeftUnit, _)  -> Holds
    -- 'substitute' returns the term as it is for the empty substitution.
    (SubstRightUnit, _) -> Holds
    -- Both sides reorder binders through the same generic traversal, except
    -- where 'substitute' stops at an empty substitution under a binder and
    -- 'rbind' does not. For a β-substitution @s1@ this is rare, from one
    -- case in several hundred to none in 20000.
    (SubstituteAgreesWithRbind, Just (Beta, _)) -> Unstable
      "substitute and rbind reorder alike, except below an empty substitution"
    _ -> genericPatternOrder
  describe "functor" $ functorSpec termSyntax (\_ _ -> genericSinkableCrash) $ \cls -> \case
    SinkAgreesWithLiftRM -> genericSinkAgreesWithLiftRM cls
    _                    -> genericPatternOrder
