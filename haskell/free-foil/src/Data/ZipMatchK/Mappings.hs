{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module Data.ZipMatchK.Mappings where

import           Data.Kind              (Type)
import           Generics.Kind

type ZipLoT :: LoT k -> LoT k -> LoT k
type family ZipLoT as bs where
  ZipLoT LoT0 LoT0 = LoT0
  ZipLoT (a :&&: as) (b :&&: bs) = ((a, b) :&&: ZipLoT as bs)

type Mappings :: LoT k -> LoT k -> LoT k -> Type
data Mappings (as :: LoT k) (bs :: LoT k) (cs :: LoT k) where
  M0 :: Mappings LoT0 LoT0 LoT0
  (:^:) :: (a -> b -> Maybe c) -> Mappings as bs cs -> Mappings (a :&&: as) (b :&&: bs) (c :&&: cs)

class PairMappings (as :: LoT k) (bs :: LoT k) where
  pairMappings :: Mappings as bs (ZipLoT as bs)

instance PairMappings LoT0 LoT0 where
  pairMappings = M0

instance PairMappings as bs => PairMappings ((a :: Type) :&&: as) ((b :: Type) :&&: bs) where
  pairMappings = (\x y -> Just (x, y)) :^: pairMappings

class ApplyMappings (v :: TyVar d Type) where
  applyMappings :: forall (as :: LoT d) (bs :: LoT d) (cs :: LoT d).
    Mappings as bs cs -> Interpret (Var v) as -> Interpret (Var v) bs -> Maybe (Interpret (Var v) cs)

instance ApplyMappings (VZ :: TyVar (Type -> tys) Type) where
  applyMappings (f :^: _) x y = f x y

instance ApplyMappings v => ApplyMappings (VS v :: TyVar (ty -> tys) Type) where
  applyMappings (_ :^: fs) x y = applyMappings @_ @v fs x y
