{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- | Kind-polymorphic syntactic (first-order) unification.
module Data.ZipMatchK (
  module Data.ZipMatchK.Mappings,
  ZipMatchK(..),
  zipMatchK,
  -- * Specializations
  -- ** Unification of plain 'Data.Kind.Type's
  zipMatchViaEq,
  zipMatchViaChooseLeft,
  -- ** Unification of 'Data.Functor.Functor's
  zipMatchWith1,
  zipMatch1,
  -- ** Unification of 'Data.Bifunctor.Bifunctor's
  zipMatchWith2,
  zipMatch2,
) where

import           Generics.Kind
import Data.Bitraversable

import Data.ZipMatchK.Generic
import Data.ZipMatchK.Mappings

-- | Perform one level of equality testing for two values and pair up components using @(,)@:
--
-- > zipMatchK = zipMatchWithK (\x y -> Just (,) :^: M0)
zipMatchK :: forall f as bs. (ZipMatchK f, PairMappings as bs) => f :@@: as -> f :@@: bs -> Maybe (f :@@: ZipLoT as bs)
zipMatchK = zipMatchWithK @_ @f @as @bs pairMappings

-- | Unify values via 'Eq'.
-- Can be used as an implementation of 'zipMatchWithK' when @k = 'Data.Kind.Type'@.
zipMatchViaEq :: Eq a => Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaEq _ x y
  | x == y = Just x
  | otherwise = Nothing

-- | Always successfully unify any two values of type @a@ by preferring the left value.
-- Can be used as an implementation of 'zipMatchWithK' when @k = 'Data.Kind.Type'@.
zipMatchViaChooseLeft :: Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaChooseLeft _ x _ = Just x

-- | 'zipMatchWithK' specialised to functors.
--
-- Note: 'Traversable' is a morally correct constraint here.
zipMatchWith1
  :: (Traversable f, ZipMatchK f)
  => (a -> a' -> Maybe a'')
  -> f a -> f a' -> Maybe (f a'')
zipMatchWith1 f = zipMatchWithK (f :^: M0)

-- | 'zipMatchK' specialised to functors.
--
-- Note: 'Traversable' is a morally correct constraint here.
zipMatch1 :: (Traversable f, ZipMatchK f) => f a -> f a' -> Maybe (f (a, a'))
zipMatch1 = zipMatchWith1 pairA
-- | 'zipMatchWithK' specialised to bifunctors.
--
-- Note: 'Bitraversable' is a morally correct constraint here.
zipMatchWith2
  :: (Bitraversable f, ZipMatchK f)
  => (a -> a' -> Maybe a'')
  -> (b -> b' -> Maybe b'')
  -> f a b -> f a' b' -> Maybe (f a'' b'')
zipMatchWith2 f g = zipMatchWithK (f :^: g :^: M0)

-- | 'zipMatchK' specialised to bifunctors.
--
-- Note: 'Bitraversable' is a morally correct constraint here.
zipMatch2 :: (Bitraversable f, ZipMatchK f) => f a b -> f a' b' -> Maybe (f (a, a') (b, b'))
zipMatch2 = zipMatchWith2 pairA pairA
