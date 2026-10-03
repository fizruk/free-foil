-- | The laws of the relative monad @'AST' binder sig@ and of renaming of
-- terms, for the untyped λ-calculus of "Control.Monad.Free.Foil.Example",
-- with single binders and with lists of binders as patterns.
--
-- See "Control.Monad.Free.Foil.Laws" for the statements.
module Control.Monad.Free.Foil.LawsSpec (spec) where

import           Test.Hspec

import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.ExampleSyntax (exprSyntax)
import           Control.Monad.Free.Foil.Laws

spec :: Spec
spec = do
  describe "λ-calculus with NameBinder (Control.Monad.Free.Foil.Example)" $ do
    let sg = exprSyntax genNameBinder nameBinderNames
    describe "α-equivalence" $ alphaSpec sg (const Holds)
    describe "relative monad" $ relMonadSpec sg (\_ _ -> Holds)
    describe "functor" $ functorSpec sg (\_ _ -> genericSinkableCrash) functorVerdict
  describe "λ-calculus with NameBinderList" $ do
    let sg = exprSyntax genNameBinderList nameBinderListNames
    describe "α-equivalence" $ alphaSpec sg alphaVerdict
    describe "relative monad" $ relMonadSpec sg (\_ _ -> Holds)
    describe "functor" $ functorSpec sg (\_ _ -> genericSinkableCrash) functorVerdict
  where
    -- 'liftRM' is lawful; 'sinkabilityProof' crashes before it can agree.
    functorVerdict _ SinkAgreesWithLiftRM = genericSinkableCrash
    functorVerdict _ _                    = Holds
    -- 'alphaEquiv' goes wrong on patterns of several binders;
    -- 'alphaEquivRefreshed' does not use the renamings and is fine.
    alphaVerdict AlphaEquivRefreshedAgrees = Holds
    alphaVerdict _                         = mergedBinderRenamings
