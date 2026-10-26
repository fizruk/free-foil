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
--
-- @since 0.2.0
type ZipLoT :: LoT k -> LoT k -> LoT k
type family ZipLoT as bs where
  ZipLoT LoT0 LoT0 = LoT0
  ZipLoT (a :&&: as) (b :&&: bs) = ((a, b) :&&: ZipLoT as bs)

infixr 5 :^:
type Mappings :: LoT k -> LoT k -> LoT k -> Type
-- | A collection of zipping functions for 'Data.ZipMatchK.zipMatchWithK'.
--
-- @since 0.2.0
data Mappings (as :: LoT k) (bs :: LoT k) (cs :: LoT k) where
  -- | An empty collection (when there no (more) type parameters).
  M0 :: Mappings LoT0 LoT0 LoT0
  -- | A non-empty collection (when there is at least one type parameter).
  (:^:) :: (a -> b -> Maybe c)    -- ^ Zipping for the first type parameter.
        -> Mappings as bs cs      -- ^ Zipping for other type parameters.
        -> Mappings (a :&&: as) (b :&&: bs) (c :&&: cs)

infixr 5 :%:
type Folds :: Type -> LoT k -> LoT k -> Type
-- | A collection of folding functions for 'Data.ZipMatchK.zipMatchFoldK',
-- one per type parameter, each combining two components into a monoid.
--
-- @since 0.6.0
data Folds m (as :: LoT k) (bs :: LoT k) where
  -- | An empty collection (when there are no (more) type parameters).
  F0 :: Folds m LoT0 LoT0
  -- | A non-empty collection (when there is at least one type parameter).
  (:%:) :: (a -> b -> m)          -- ^ Folding for the first type parameter.
        -> Folds m as bs          -- ^ Folding for other type parameters.
        -> Folds m (a :&&: as) (b :&&: bs)

-- | Type parameter lists that can be paired up componentwise.
--
-- @since 0.2.0
class PairMappings (as :: LoT k) (bs :: LoT k) where
  -- | A collection of pairing functions @(\\x y -> Just (x, y))@ for 'Data.ZipMatchK.zipMatchK'.
  --
  -- @since 0.2.0
  pairMappings :: Mappings as bs (ZipLoT as bs)

instance PairMappings LoT0 LoT0 where
  pairMappings = M0

instance PairMappings as bs => PairMappings ((a :: Type) :&&: as) ((b :: Type) :&&: bs) where
  pairMappings = pairA :^: pairMappings

-- | Type variables at which a collection of zipping functions can be applied.
--
-- @since 0.2.0
class ApplyMappings (v :: TyVar d Type) where
  -- | Apply a collection of zipping functions to collections of values.
  --
  -- @since 0.2.0
  applyMappings :: forall (as :: LoT d) (bs :: LoT d) (cs :: LoT d).
       Mappings as bs cs      -- ^ A collection of zipping functions.
    -> Interpret (Var v) as   -- ^ First collection of values (one per type parameter).
    -> Interpret (Var v) bs   -- ^ Second collection of values (one per type parameter).
    -> Maybe (Interpret (Var v) cs)

  -- | Apply a collection of folding functions to collections of values.
  --
  -- @since 0.6.0
  applyFolds :: forall m (as :: LoT d) (bs :: LoT d).
       Folds m as bs          -- ^ A collection of folding functions.
    -> Interpret (Var v) as   -- ^ First collection of values (one per type parameter).
    -> Interpret (Var v) bs   -- ^ Second collection of values (one per type parameter).
    -> m

instance ApplyMappings (VZ :: TyVar (Type -> tys) Type) where
  applyMappings (f :^: _) x y = f x y
  applyFolds (f :%: _) x y = f x y

instance ApplyMappings v => ApplyMappings (VS v :: TyVar (ty -> tys) Type) where
  applyMappings (_ :^: fs) x y = applyMappings @_ @v fs x y
  applyFolds (_ :%: fs) x y = applyFolds @_ @v fs x y

-- | Pair two values in a context.
--
-- @since 0.3.0
pairA :: Applicative f => a -> b -> f (a, b)
pairA x y = pure (x, y)
