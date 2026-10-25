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
  ZipMatchFoldK(..),
  zipMatchAllK,
  -- * Specializations
  -- ** Unification of plain 'Data.Kind.Type's
  zipMatchViaEq,
  zipMatchViaChooseLeft,
  -- ** Unification of 'Data.Functor.Functor's
  zipMatchWith1,
  zipMatch1,
  zipMatchFold1,
  zipMatchAll1,
  -- ** Unification of 'Data.Bifunctor.Bifunctor's
  zipMatchWith2,
  zipMatch2,
  zipMatchFold2,
  zipMatchAll2,
) where

import           Data.Coerce (coerce)
import           Data.Monoid (All (..))
import           Generics.Kind
import Data.Bitraversable

import Data.ZipMatchK.Generic
import Data.ZipMatchK.Mappings

-- | Perform one level of equality testing for two values and pair up components using @(,)@:
--
-- > zipMatchK = zipMatchWithK (\x y -> Just (,) :^: M0)
--
-- @since 0.2.0
zipMatchK :: forall f as bs. (ZipMatchK f, PairMappings as bs) => f :@@: as -> f :@@: bs -> Maybe (f :@@: ZipLoT as bs)
zipMatchK = zipMatchWithK @_ @f @as @bs pairMappings

-- | Unify values via 'Eq'.
-- Can be used as an implementation of 'zipMatchWithK' when @k = 'Data.Kind.Type'@.
--
-- @since 0.2.0
zipMatchViaEq :: Eq a => Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaEq _ x y
  | x == y = Just x
  | otherwise = Nothing

-- | Always successfully unify any two values of type @a@ by preferring the left value.
-- Can be used as an implementation of 'zipMatchWithK' when @k = 'Data.Kind.Type'@.
--
-- @since 0.2.0
zipMatchViaChooseLeft :: Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaChooseLeft _ x _ = Just x

-- | 'zipMatchWithK' specialised to functors.
--
-- Note: 'Traversable' is a morally correct constraint here.
--
-- @since 0.3.0
zipMatchWith1
  :: (Traversable f, ZipMatchK f)
  => (a -> a' -> Maybe a'')
  -> f a -> f a' -> Maybe (f a'')
zipMatchWith1 f = zipMatchWithK (f :^: M0)

-- | 'zipMatchK' specialised to functors.
--
-- Note: 'Traversable' is a morally correct constraint here.
--
-- @since 0.3.0
zipMatch1 :: (Traversable f, ZipMatchK f) => f a -> f a' -> Maybe (f (a, a'))
zipMatch1 = zipMatchWith1 pairA
-- | 'zipMatchWithK' specialised to bifunctors.
--
-- Note: 'Bitraversable' is a morally correct constraint here.
--
-- @since 0.3.0
zipMatchWith2
  :: (Bitraversable f, ZipMatchK f)
  => (a -> a' -> Maybe a'')
  -> (b -> b' -> Maybe b'')
  -> f a b -> f a' b' -> Maybe (f a'' b'')
zipMatchWith2 f g = zipMatchWithK (f :^: g :^: M0)

-- | 'zipMatchK' specialised to bifunctors.
--
-- Note: 'Bitraversable' is a morally correct constraint here.
--
-- @since 0.3.0
zipMatch2 :: (Bitraversable f, ZipMatchK f) => f a b -> f a' b' -> Maybe (f (a, a') (b, b'))
zipMatch2 = zipMatchWith2 pairA pairA

-- | 'zipMatchFoldK' specialised to functors.
--
-- >>> zipMatchFold1 (\x y -> [x + y]) (Just 1) (Just (2 :: Int))
-- Just [3]
-- >>> zipMatchFold1 (\x y -> [x + y]) [1, 2] [10, 20 :: Int]
-- Just [11,22]
-- >>> zipMatchFold1 (\x y -> [x + y]) [1, 2] [10 :: Int]
-- Nothing
--
-- @since 0.5.1
zipMatchFold1
  :: (ZipMatchFoldK f, Monoid m)
  => (a -> a' -> m)
  -> f a -> f a' -> Maybe m
zipMatchFold1 f = zipMatchFoldK (f :%: F0)

-- | 'zipMatchFoldK' specialised to bifunctors. With 'Data.Monoid.All' it
-- checks that two nodes have the same constructor and that their components
-- satisfy a relation, without building anything for the components:
--
-- >>> import Data.Monoid (All (..))
-- >>> let same = zipMatchFold2 (\x y -> All (x == y)) (\x y -> All (x == y))
-- >>> getAll <$> same (Left 1) (Left (1 :: Int) :: Either Int Int)
-- Just True
-- >>> getAll <$> same (Left 1) (Left (2 :: Int) :: Either Int Int)
-- Just False
-- >>> getAll <$> same (Left 1) (Right (1 :: Int) :: Either Int Int)
-- Nothing
--
-- @since 0.5.1
zipMatchFold2
  :: (ZipMatchFoldK f, Monoid m)
  => (a -> a' -> m)
  -> (b -> b' -> m)
  -> f a b -> f a' b' -> Maybe m
zipMatchFold2 f g = zipMatchFoldK (f :%: g :%: F0)

-- | Check a relation on all paired components: 'Nothing' when the shapes
-- differ, as for 'zipMatchFoldK', and otherwise whether every component
-- satisfies its relation. The components are checked left to right, and the
-- check stops at the first that fails.
--
-- > zipMatchAllK = fmap getAll . zipMatchFoldK (coerce relations)
--
-- @since 0.5.1
zipMatchAllK :: forall f as bs. ZipMatchFoldK f => Folds Bool as bs -> f :@@: as -> f :@@: bs -> Maybe Bool
zipMatchAllK relations x y = getAll <$> zipMatchFoldK @_ @f @as @bs (coerce relations) x y
{-# INLINE zipMatchAllK #-}

-- | 'zipMatchAllK' specialised to functors.
--
-- >>> zipMatchAll1 (==) (Just 1) (Just (1 :: Int))
-- Just True
-- >>> zipMatchAll1 (==) [1, 2] [1, 3 :: Int]
-- Just False
-- >>> zipMatchAll1 (==) [1, 2] [1 :: Int]
-- Nothing
--
-- @since 0.5.1
zipMatchAll1 :: ZipMatchFoldK f => (a -> a' -> Bool) -> f a -> f a' -> Maybe Bool
zipMatchAll1 f = zipMatchAllK (f :%: F0)
{-# INLINE zipMatchAll1 #-}

-- | 'zipMatchAllK' specialised to bifunctors.
--
-- >>> zipMatchAll2 (==) (==) (Left 1) (Left (1 :: Int) :: Either Int Int)
-- Just True
-- >>> zipMatchAll2 (==) (==) (Left 1) (Right (1 :: Int) :: Either Int Int)
-- Nothing
--
-- @since 0.5.1
zipMatchAll2
  :: ZipMatchFoldK f
  => (a -> a' -> Bool)
  -> (b -> b' -> Bool)
  -> f a b -> f a' b' -> Maybe Bool
zipMatchAll2 f g = zipMatchAllK (f :%: g :%: F0)
{-# INLINE zipMatchAll2 #-}
