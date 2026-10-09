{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
-- | This module provides 'GenericK' and 'ZipMatchK' instances for 'Sum' and 'Product',
-- to enable the use of 'ZipMatchK' with the data types à la carte approach.
--
-- The 'ZipMatchK' instances are written out, in the form that
-- "Data.ZipMatchK.TH" derives, rather than taken from the generic default,
-- which converts every node to its "Generics.Kind" representation and back.
module Data.ZipMatchK.Functor where

import Data.Kind (Type)
import Generics.Kind
import Data.Functor.Sum
import Data.Functor.Product

import Data.ZipMatchK

instance GenericK (Sum f g) where
  type RepK (Sum f g) =
    Field (Kon f :@: Var0)
    :+: Field (Kon g :@: Var0)
instance GenericK (Product f g) where
  type RepK (Product f g) =
    Field (Kon f :@: Var0)
    :*: Field (Kon g :@: Var0)

-- | Note: instance is limited to 'Type'-kinded functors @f@ and @g@.
instance (ZipMatchK f, ZipMatchK g) => ZipMatchK (Sum f (g :: Type -> Type)) where
  zipMatchWithK mappings@(_ :^: M0) l r = case (l, r) of
    (InL x, InL y) -> InL <$> zipMatchWithK @_ @f mappings x y
    (InR x, InR y) -> InR <$> zipMatchWithK @_ @g mappings x y
    _              -> Nothing

-- | Note: instance is limited to 'Type'-kinded functors @f@ and @g@.
instance (ZipMatchK f, ZipMatchK g) => ZipMatchK (Product f (g :: Type -> Type)) where
  zipMatchWithK mappings@(_ :^: M0) (Pair x1 x2) (Pair y1 y2) =
    Pair <$> zipMatchWithK @_ @f mappings x1 y1 <*> zipMatchWithK @_ @g mappings x2 y2
