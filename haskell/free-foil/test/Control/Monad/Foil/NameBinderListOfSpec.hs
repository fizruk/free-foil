{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE RankNTypes      #-}
-- | 'Foil.nameBinderListOf' at the types where rewrite rules replace it:
-- 'Foil.NameBinderList' and 'Foil.NameBinders'. With optimisation on, the
-- calls at a known type below go through the rules, and the reference goes
-- through 'Foil.withPattern', so the two must list the same binders in the
-- same order.
module Control.Monad.Foil.NameBinderListOfSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import qualified Control.Monad.Foil       as Foil
import           Control.Monad.Foil.Laws

-- | The binders of a pattern, collected by 'Foil.withPattern' as
-- 'Foil.nameBinderListOf' does when no rule applies. Not inlined, so that it
-- is compiled once, for an unknown pattern type.
{-# NOINLINE viaWithPattern #-}
viaWithPattern :: Foil.CoSinkable p => p n l -> [Int]
viaWithPattern pat = Foil.withPattern
  (\scope binder k -> Foil.withFresh scope $ \binder' ->
      k (Names (Foil.nameId (Foil.nameOf binder) :)) binder')
  (Names id)
  (\(Names f) (Names g) -> Names (f . g))
  Foil.emptyScope
  pat
  (\(Names f) _ _ -> f [])

-- | A difference list of raw names, indexed like the results of
-- 'Foil.withPattern'.
newtype Names (n :: Foil.S) (l :: Foil.S) (o :: Foil.S) (o' :: Foil.S) = Names ([Int] -> [Int])

-- | Both listings of the binders of generated patterns.
agree :: Foil.CoSinkable p => (forall n l. p n l -> [Int]) -> GenPattern p -> Property
agree listed gen = forAllShow genCtx (\(SomeCtx ctx) -> showCtx ctx) $ \(SomeCtx ctx) ->
  forAllShow (gen ctx) (\(PatIn pat) -> showPatternWith viaWithPattern pat) $ \(PatIn pat) ->
    listed pat === viaWithPattern pat

spec :: Spec
spec = describe "nameBinderListOf" $ do
  it "at NameBinderList, lists the binders in order" $
    agree (nameBinderListNames . Foil.nameBinderListOf) genNameBinderList
  it "at NameBinders, lists the binders as withPattern does" $
    agree (nameBinderListNames . Foil.nameBinderListOf) genNameBinders
  where
    genNameBinders :: GenPattern Foil.NameBinders
    genNameBinders ctx = do
      PatIn binders <- genNameBinderList ctx
      pure (PatIn (Foil.fromNameBindersList binders))
