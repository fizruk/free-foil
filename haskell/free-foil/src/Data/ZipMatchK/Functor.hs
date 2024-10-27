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

-- | Note: instance is limited to 'Type'-kinded bifunctors @f@ and @g@.
instance (Traversable f, Traversable g, ZipMatchK f, ZipMatchK g) => ZipMatchK (Sum f (g :: Type -> Type))
-- | Note: instance is limited to 'Type'-kinded bifunctors @f@ and @g@.
instance (Traversable f, Traversable g, ZipMatchK f, ZipMatchK g) => ZipMatchK (Product f (g :: Type -> Type))
