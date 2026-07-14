{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Helpers for 'Foil.NameMap' and 'Foil.NameBinderList'.
module Control.Monad.Foil.NameMapSpec (spec) where

import           Data.Foldable      (toList)
import           Test.Hspec

import qualified Control.Monad.Foil as Foil

-- | The raw names bound by a list of binders, outermost first.
binderIds :: Foil.NameBinderList n l -> [Int]
binderIds Foil.NameBinderListEmpty = []
binderIds (Foil.NameBinderListCons binder binders) =
  Foil.nameId (Foil.nameOf binder) : binderIds binders

spec :: Spec
spec = do
  describe "withFreshNameBinderList" $ do
    it "binds each value to a fresh binder, in order" $
      Foil.withFreshNameBinderList "abc" Foil.emptyScope Foil.emptyNameMap $
        \_scope binders nameMap -> do
          binderIds binders `shouldBe` [0, 1, 2]   -- a fresh name is max scope + 1
          toList nameMap `shouldBe` "abc"

    it "binds nothing when there is nothing to bind" $
      Foil.withFreshNameBinderList ([] :: [Int]) Foil.emptyScope Foil.emptyNameMap $
        \_scope binders nameMap -> do
          binderIds binders `shouldBe` []
          toList nameMap `shouldBe` []

  describe "popNameBinder" $
    it "undoes addNameBinder" $
      Foil.withFresh Foil.emptyScope $ \binder ->
        let nameMap = Foil.addNameBinder binder 'x' Foil.emptyNameMap
         in toList (Foil.popNameBinder binder nameMap) `shouldBe` ""

  describe "snocNameBinderList" $
    it "adds a binder to the innermost position" $
      Foil.withFreshNameBinderList "ab" Foil.emptyScope Foil.emptyNameMap $
        \scope binders _nameMap ->
          Foil.withFresh scope $ \binder ->
            binderIds (Foil.snocNameBinderList binders binder) `shouldBe` [0, 1, 2]

  describe "concatNameBinderLists" $
    it "agrees with snocNameBinderList on a singleton" $
      Foil.withFreshNameBinderList "ab" Foil.emptyScope Foil.emptyNameMap $
        \scope binders _nameMap ->
          Foil.withFresh scope $ \binder ->
            let singleton = Foil.NameBinderListCons binder Foil.NameBinderListEmpty
             in binderIds (Foil.concatNameBinderLists binders singleton)
                  `shouldBe` binderIds (Foil.snocNameBinderList binders binder)
