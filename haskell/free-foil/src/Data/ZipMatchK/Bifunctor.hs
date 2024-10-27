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
module Data.ZipMatchK.Bifunctor where

import Data.Kind (Type)
import Generics.Kind
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

instance (ZipMatchK f, ZipMatchK g) => ZipMatchK (Sum (f :: Type -> Type -> Type) g)
instance (ZipMatchK f, ZipMatchK g) => ZipMatchK (Product (f :: Type -> Type -> Type) g)
