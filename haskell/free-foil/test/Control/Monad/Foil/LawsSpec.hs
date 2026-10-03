{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
-- | The laws of 'Foil.Sinkable' and 'Foil.CoSinkable' for the types of the
-- foil itself: names, sets of names, and the shipped pattern types.
--
-- See "Control.Monad.Foil.Laws" for the statements, and
-- "Control.Monad.Free.Foil.LawsSpec" for terms.
module Control.Monad.Foil.LawsSpec (spec) where

import           Data.Functor.Compose        (Compose (..))
import           Test.Hspec
import           Test.QuickCheck

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Foil.Internal (U2 (..))
import           Control.Monad.Foil.Laws

-- | Lists of names, through the 'Compose' instance.
genNames :: Ctx n -> Gen (Compose [] Foil.Name n)
genNames ctx = case ctxNames ctx of
  [] -> pure (Compose [])
  xs -> Compose <$> listOf (elements xs)

-- | Sets of names.
genNameSet :: Ctx n -> Gen (Foil.NameSet n)
genNameSet ctx = Foil.nameSetFromList <$> sublistOf (ctxNames ctx)

-- | Unordered sets of binders, from a list.
genNameBinders :: GenPattern Foil.NameBinders
genNameBinders ctx = do
  PatIn binders <- genNameBinderList ctx
  pure (PatIn (Foil.fromNameBindersList binders))

-- | The wildcard pattern.
genU2 :: GenPattern U2
genU2 ctx = withCtx ctx $ \_ -> pure (PatIn U2)

spec :: Spec
spec = do
  describe "Sinkable" $ do
    describe "[Name] (via Compose)" $
      sinkableSpec
        (\_ (Compose xs) (Compose ys) -> map Foil.nameId xs == map Foil.nameId ys)
        (\(Compose xs) -> unwords (map showName xs))
        genNames
        (\(Compose xs) -> map Compose (shrinkList (const []) xs))
        (\_ _ -> Holds)
    describe "NameSet" $
      sinkableSpec
        (\_ xs ys -> map Foil.nameId (Foil.nameSetToList xs) == map Foil.nameId (Foil.nameSetToList ys))
        (unwords . map showName . Foil.nameSetToList)
        genNameSet
        (const [])
        (\_ _ -> Holds)

  describe "CoSinkable" $ do
    describe "NameBinder" $ coSinkableSpec nameBinderNames genNameBinder extensionByCoercion
    describe "NameBinderList" $ coSinkableSpec nameBinderListNames genNameBinderList extensionByCoercion
    describe "NameBinders" $ coSinkableSpec patternRawNames genNameBinders extensionByCoercion
    describe "U2" $ coSinkableSpec (const []) genU2 (\_ _ -> Holds)

  describe "UnifiablePattern" $ do
    describe "NameBinder" $ unifyPatternsSpec nameBinderNames genNameBinderPair Holds
    describe "NameBinderList" $
      unifyPatternsSpec nameBinderListNames genNameBinderListPair mergedBinderRenamings

-- | Two single binders out of the same scope.
genNameBinderPair :: GenPatternPair Foil.NameBinder
genNameBinderPair ctx = do
  PatIn l <- genNameBinder ctx
  PatIn r <- genNameBinder ctx
  pure (PatPair l r)
