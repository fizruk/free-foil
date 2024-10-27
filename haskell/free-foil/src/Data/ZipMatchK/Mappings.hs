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

-- | Zip to lists of types into a single list of pair types.
type ZipLoT :: LoT k -> LoT k -> LoT k
type family ZipLoT as bs where
  ZipLoT LoT0 LoT0 = LoT0
  ZipLoT (a :&&: as) (b :&&: bs) = ((a, b) :&&: ZipLoT as bs)

infixr 5 :^:
type Mappings :: LoT k -> LoT k -> LoT k -> Type
-- | A collection of zipping functions for 'Data.ZipMatchK.zipMatchWithK'.
data Mappings (as :: LoT k) (bs :: LoT k) (cs :: LoT k) where
  -- | An empty collection (when there no (more) type parameters).
  M0 :: Mappings LoT0 LoT0 LoT0
  -- | A non-empty collection (when there is at least one type parameter).
  (:^:) :: (a -> b -> Maybe c)    -- ^ Zipping for the first type parameter.
        -> Mappings as bs cs      -- ^ Zipping for other type parameters.
        -> Mappings (a :&&: as) (b :&&: bs) (c :&&: cs)

class PairMappings (as :: LoT k) (bs :: LoT k) where
  -- | A collection of pairing functions @(\\x y -> Just (x, y))@ for 'Data.ZipMatchK.zipMatchK'.
  pairMappings :: Mappings as bs (ZipLoT as bs)

instance PairMappings LoT0 LoT0 where
  pairMappings = M0

instance PairMappings as bs => PairMappings ((a :: Type) :&&: as) ((b :: Type) :&&: bs) where
  pairMappings = pairA :^: pairMappings

class ApplyMappings (v :: TyVar d Type) where
  -- | Apply a collection of zipping functions to collections of values.
  applyMappings :: forall (as :: LoT d) (bs :: LoT d) (cs :: LoT d).
       Mappings as bs cs      -- ^ A collection of zipping functions.
    -> Interpret (Var v) as   -- ^ First collection of values (one per type parameter).
    -> Interpret (Var v) bs   -- ^ Second collection of values (one per type parameter).
    -> Maybe (Interpret (Var v) cs)

instance ApplyMappings (VZ :: TyVar (Type -> tys) Type) where
  applyMappings (f :^: _) x y = f x y

instance ApplyMappings v => ApplyMappings (VS v :: TyVar (ty -> tys) Type) where
  applyMappings (_ :^: fs) x y = applyMappings @_ @v fs x y

-- | Pair two values in a context.
pairA :: Applicative f => a -> b -> f (a, b)
pairA x y = pure (x, y)
