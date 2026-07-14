{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | The derived 'ZipMatchK' instance must agree with the generic one.
--
-- Both are available for the same type: 'deriveZipMatchK' provides the
-- instance, and 'genericZipMatchWithK' computes the generic answer without
-- needing one. So the test compares the two, on every pair of a set of sample
-- values, over the field shapes a signature actually uses.
module Data.ZipMatchK.THSpec (spec) where

import           Data.List.NonEmpty      (NonEmpty (..))
import           Generics.Kind           (LoT (..))
import qualified GHC.Generics            as GHC
import           Generics.Kind.TH        (deriveGenericK)
import           Test.Hspec

import           Data.ZipMatchK
import           Data.ZipMatchK.Generic  (genericZipMatchWithK)
import           Data.ZipMatchK.TH

-- | An annotation, standing for the extra parameter a generated signature has.
newtype Ann = Ann Int deriving (Eq, Show)
instance ZipMatchK Ann where zipMatchWithK = zipMatchViaEq

-- | A signature exercising every field shape the deriver has to compile: a
-- term, a scoped term, a constant, the extra parameter, a container of terms,
-- a container of scoped terms, and a nest of containers.
data RichSig a scope term
  = AppSig term term
  | LamSig scope
  | LitSig Ann
  | AnnSig a term
  | ManySig [term]
  | SomeSig (Maybe scope)
  | NestSig [Maybe term]
  | NonEmptySig (NonEmpty term)
  | EitherSig (Either Ann term)
  | PairSig (scope, term)
  | NullarySig
  deriving (GHC.Generic, Functor, Foldable, Traversable, Eq, Show)

deriveGenericK ''RichSig
deriveZipMatchK2 ''RichSig

-- | A plain signature bifunctor, with no extra parameters.
data LamSig scope term = App term term | Lam scope
  deriving (GHC.Generic, Functor, Foldable, Traversable, Eq, Show)

deriveGenericK ''LamSig
deriveZipMatchK ''LamSig

-- | A functor, as an annotation would be.
newtype Boxed term = Boxed [term]
  deriving (GHC.Generic, Functor, Foldable, Traversable, Eq, Show)

deriveGenericK ''Boxed
deriveZipMatchK1 ''Boxed

-- | Zip two values by equality, so that a zipped signature has the same type as
-- the signatures it came from, and can be compared with '=='.
zipEq :: Eq a => a -> a -> Maybe a
zipEq x y
  | x == y    = Just x
  | otherwise = Nothing

richSamples :: [RichSig Ann String String]
richSamples =
  [ AppSig "x" "y"
  , AppSig "x" "z"
  , LamSig "s"
  , LamSig "t"
  , LitSig (Ann 1)
  , LitSig (Ann 2)
  , AnnSig (Ann 1) "x"
  , AnnSig (Ann 2) "x"
  , ManySig []
  , ManySig ["x"]
  , ManySig ["x", "y"]
  , SomeSig Nothing
  , SomeSig (Just "s")
  , NestSig [Just "x", Nothing]
  , NestSig [Just "y", Nothing]
  , NonEmptySig ("x" :| [])
  , NonEmptySig ("x" :| ["y"])
  , EitherSig (Left (Ann 1))
  , EitherSig (Right "x")
  , PairSig ("s", "x")
  , NullarySig
  ]

lamSamples :: [LamSig String String]
lamSamples = [App "x" "y", App "x" "x", Lam "s", Lam "t"]

boxedSamples :: [Boxed String]
boxedSamples = [Boxed [], Boxed ["x"], Boxed ["x", "y"]]

spec :: Spec
spec = do
  describe "deriveZipMatchK2" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @(RichSig Ann) mappings x y
            `shouldBe` genericZipMatchWithK @(RichSig Ann) mappings x y
        | x <- richSamples, y <- richSamples ]

  describe "deriveZipMatchK" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @LamSig mappings x y
            `shouldBe` genericZipMatchWithK @LamSig mappings x y
        | x <- lamSamples, y <- lamSamples ]

  describe "deriveZipMatchK1" $
    it "agrees with the generic instance on every pair of samples" $
      sequence_
        [ zipMatchWithK @_ @Boxed (zipEq :^: M0) x y
            `shouldBe` genericZipMatchWithK @Boxed (zipEq :^: M0) x y
        | x <- boxedSamples, y <- boxedSamples ]
  where
    mappings :: Mappings (String ':&&: String ':&&: 'LoT0) (String ':&&: String ':&&: 'LoT0) (String ':&&: String ':&&: 'LoT0)
    mappings = zipEq :^: zipEq :^: M0
