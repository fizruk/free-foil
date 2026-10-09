{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

-- | The written-out 'ZipMatchK' instances for 'Sum' and 'Product' must agree
-- with the generic ones, which 'genericZipMatchWithK' still computes from the
-- 'Generics.Kind.GenericK' instances. As in "Data.ZipMatchK.THSpec", the test
-- compares the two on every pair of a set of sample values.
module Data.ZipMatchK.SumProductSpec (spec) where

import qualified Data.Bifunctor.Product   as Bi
import qualified Data.Bifunctor.Sum       as Bi
import qualified Data.Functor.Product     as F
import qualified Data.Functor.Sum         as F
import           Generics.Kind            (LoT (..))
import           Test.Hspec

import           Data.ZipMatchK
import           Data.ZipMatchK.Bifunctor ()
import           Data.ZipMatchK.Functor   ()
import           Data.ZipMatchK.Generic   (genericZipMatchWithK)
import           Data.ZipMatchK.TH

-- | A signature bifunctor.
data LamSig scope term = App term term | Lam scope
  deriving (Functor, Foldable, Traversable, Eq, Show)

deriveZipMatchK ''LamSig

-- | A functor.
newtype Boxed term = Boxed [term]
  deriving (Functor, Foldable, Traversable, Eq, Show)

deriveZipMatchK1 ''Boxed

-- | Zip two values by equality, so that the result has the same type as the
-- inputs and can be compared with '=='.
zipEq :: Eq a => a -> a -> Maybe a
zipEq x y
  | x == y    = Just x
  | otherwise = Nothing

lamSamples :: [LamSig String String]
lamSamples = [App "x" "y", App "x" "x", Lam "s", Lam "t"]

boxedSamples :: [Boxed String]
boxedSamples = [Boxed [], Boxed ["x"], Boxed ["x", "y"]]

spec :: Spec
spec = do
  describe "Data.Bifunctor.Sum" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @(Bi.Sum LamSig LamSig) mappings2 x y
            `shouldBe` genericZipMatchWithK @(Bi.Sum LamSig LamSig) mappings2 x y
        | let samples = map Bi.L2 lamSamples ++ map Bi.R2 lamSamples
        , x <- samples, y <- samples ]

  describe "Data.Bifunctor.Product" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @(Bi.Product LamSig LamSig) mappings2 x y
            `shouldBe` genericZipMatchWithK @(Bi.Product LamSig LamSig) mappings2 x y
        | let samples = [Bi.Pair a b | a <- lamSamples, b <- lamSamples]
        , x <- samples, y <- samples ]

  describe "Data.Functor.Sum" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @(F.Sum Boxed Boxed) (zipEq :^: M0) x y
            `shouldBe` genericZipMatchWithK @(F.Sum Boxed Boxed) (zipEq :^: M0) x y
        | let samples = map F.InL boxedSamples ++ map F.InR boxedSamples
        , x <- samples, y <- samples ]

  describe "Data.Functor.Product" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @(F.Product Boxed Boxed) (zipEq :^: M0) x y
            `shouldBe` genericZipMatchWithK @(F.Product Boxed Boxed) (zipEq :^: M0) x y
        | let samples = [F.Pair a b | a <- boxedSamples, b <- boxedSamples]
        , x <- samples, y <- samples ]
  where
    mappings2 :: Mappings (String ':&&: String ':&&: 'LoT0) (String ':&&: String ':&&: 'LoT0) (String ':&&: String ':&&: 'LoT0)
    mappings2 = zipEq :^: zipEq :^: M0
