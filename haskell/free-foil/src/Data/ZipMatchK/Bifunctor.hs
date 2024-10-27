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
-- | This module provides 'GenericK' and 'ZipMatchK' instances for 'Sum' and 'Product',
-- to enable the use of 'ZipMatchK' with the data types à la carte approach.
module Data.ZipMatchK.Bifunctor where

import Data.Kind (Type)
import Generics.Kind
import Data.Bitraversable
import Data.Bifunctor.Sum
import Data.Bifunctor.Product

import Data.ZipMatchK

instance GenericK (Sum f g) where
  type RepK (Sum f g) =
    Field ((Kon f :@: Var0) :@: Var1)
    :+: Field ((Kon g :@: Var0) :@: Var1)
instance GenericK (Product f g) where
  type RepK (Product f g) =
    Field ((Kon f :@: Var0) :@: Var1)
    :*: Field ((Kon g :@: Var0) :@: Var1)

-- | Note: instance is limited to 'Type'-kinded bifunctors @f@ and @g@.
instance (Bitraversable f, Bitraversable g, ZipMatchK f, ZipMatchK g) => ZipMatchK (Sum f (g :: Type -> Type -> Type))
-- | Note: instance is limited to 'Type'-kinded bifunctors @f@ and @g@.
instance (Bitraversable f, Bitraversable g, ZipMatchK f, ZipMatchK g) => ZipMatchK (Product f (g :: Type -> Type -> Type))
