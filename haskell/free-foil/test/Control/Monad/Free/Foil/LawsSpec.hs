{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | The laws of the relative monad @'AST' binder sig@ and of renaming of
-- terms, for the untyped λ-calculus of "Control.Monad.Free.Foil.Example",
-- with single binders and with lists of binders as patterns.
--
-- See "Control.Monad.Free.Foil.Laws" for the statements.
module Control.Monad.Free.Foil.LawsSpec (spec) where

import           Data.Bifunctor.TH               (deriveBifoldable, deriveBitraversable)
import           Test.Hspec

import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Example (ExprF (..))
import           Control.Monad.Free.Foil.Laws
import           Data.ZipMatchK.TH               (deriveZipMatchK)

deriveBifoldable ''ExprF
deriveBitraversable ''ExprF
deriveZipMatchK ''ExprF

-- | The λ-calculus, with a given kind of pattern.
exprSyntax :: GenPattern binder -> SyntaxGen binder ExprF
exprSyntax genPat = SyntaxGen
  { sgShapes = [AppF () (), LamF ()]
  , sgPattern = genPat
  , sgShowNode = \case
      AppF f x  -> "(" <> f <> " " <> x <> ")"
      LamF body -> body
  }

spec :: Spec
spec = do
  describe "λ-calculus with NameBinder (Control.Monad.Free.Foil.Example)" $ do
    let sg = exprSyntax genNameBinder
    describe "α-equivalence" $ alphaSpec sg (const Holds)
    describe "relative monad" $ relMonadSpec sg (const Holds)
    describe "functor" $ functorSpec sg (\_ _ -> genericSinkableCrash) functorVerdict
  describe "λ-calculus with NameBinderList" $ do
    let sg = exprSyntax genNameBinderList
    describe "α-equivalence" $ alphaSpec sg alphaVerdict
    describe "relative monad" $ relMonadSpec sg (const Holds)
    describe "functor" $ functorSpec sg (\_ _ -> genericSinkableCrash) functorVerdict
  where
    -- 'liftRM' is lawful; 'sinkabilityProof' crashes before it can agree.
    functorVerdict _ SinkAgreesWithLiftRM = genericSinkableCrash
    functorVerdict _ _                    = Holds
    -- 'alphaEquiv' goes wrong on patterns of several binders;
    -- 'alphaEquivRefreshed' does not use the renamings and is fine.
    alphaVerdict AlphaEquivRefreshedAgrees = Holds
    alphaVerdict _                         = mergedBinderRenamings
