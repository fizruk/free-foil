{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.ZipMatchK (
  module Data.ZipMatchK.Mappings,
  ZipMatchK(..),
  zipMatchK,
  zipMatch2,
  zipMatchViaEq,
  zipMatchViaChooseLeft,
) where

import           Generics.Kind

import Data.ZipMatchK.Generic
import Data.ZipMatchK.Mappings

zipMatchK :: forall f as bs. (ZipMatchK f, PairMappings as bs) => f :@@: as -> f :@@: bs -> Maybe (f :@@: ZipLoT as bs)
zipMatchK = zipMatchWithK @_ @f @as @bs pairMappings

zipMatch2 :: forall f a b a' b'. (ZipMatchK f) => f a b -> f a' b' -> Maybe (f (a, a') (b, b'))
zipMatch2 = zipMatchK @f @(a :&&: b :&&: LoT0) @(a' :&&: b' :&&: LoT0)

zipMatchViaEq :: Eq a => Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaEq _ x y
  | x == y = Just x
  | otherwise = Nothing

zipMatchViaChooseLeft :: Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaChooseLeft _ x _ = Just x
