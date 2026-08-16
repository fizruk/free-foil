{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Deterministic stripe assignment for separately checked units.
--
-- A module system wants each unit to allocate its top-level names inside its
-- own reservation (see "Control.Monad.Foil.Blocks"), and it wants the
-- assignment of reservations to be /deterministic/: a unit's declarations are
-- numbered @base@, @base + 1@, … in declaration order, whatever else is
-- checked around it. Determinism is what makes raw names cacheable — a unit
-- checked today and a unit loaded tomorrow agree name for name — and what
-- discharges the trust obligation of 'Control.Monad.Foil.Blocks.checkExtScope',
-- which compares raw names across independently built worlds.
--
-- The registry is that assignment: an append-only map from unit names to
-- stripe indices, handing out the next index on first use. In a real build it
-- is persisted beside the build products, because cached artifacts survive
-- changes elsewhere in the build exactly when the assignment does not move.
-- Where the stripes lie on the raw-name line is a 'StripeLayout', a client
-- policy: the library is region-agnostic, and the allocator admits negative
-- names.
module Control.Monad.Foil.Registry (
  -- * Stripe indices
  StripeIndex (..),
  -- * Layouts
  StripeLayout (..),
  stripesBelowZero,
  stripesAbove,
  -- * The registry
  Registry,
  emptyRegistry,
  registrySize,
  registerUnit,
) where

import           Data.Binary                 (Binary)
import           Data.Map                    (Map)
import qualified Data.Map                    as Map

import           Control.Monad.Foil.Internal (NameRange (..))

-- $setup
-- >>> import Control.Monad.Foil.Internal

-- | A stripe's position in the registry: which run of names a unit draws
-- from. Its own type, so that a stripe index cannot be confused with a name,
-- a count, or an offset.
newtype StripeIndex = StripeIndex Int
  deriving newtype (Eq, Ord, Show, Read, Binary)

-- | Where stripe @i@ lies on the raw-name line.
--
-- The library does not choose: whether stripes descend below zero, ascend
-- from some base, or interleave with other reservations is a policy of the
-- client, and everything in "Control.Monad.Foil.Blocks" works from the
-- resulting 'NameRange's alone. A layout should give disjoint ranges to
-- distinct indices; nothing checks this here, but
-- 'Control.Monad.Foil.Blocks.withDisjointUnion' refuses the overlap at the
-- point where it would do harm.
newtype StripeLayout = StripeLayout
  { stripeRange :: StripeIndex -> NameRange
  }

-- | Stripe @i@ is the @i@-th run of @size@ names below zero, counting
-- downwards, so stripe 0 is @[-size .. -1]@. Within a stripe, allocation
-- still ascends (see 'Control.Monad.Foil.withFreshIn'), so declaration order
-- is ascending name order.
--
-- This layout leaves the whole non-negative range free for a client's local
-- names, which is what
-- <https://github.com/fizruk/free-foil the mltt demo> uses it for.
--
-- >>> stripeRange (stripesBelowZero 100) (StripeIndex 0)
-- NameRange {nameRangeLo = -100, nameRangeHi = -1}
-- >>> stripeRange (stripesBelowZero 100) (StripeIndex 2)
-- NameRange {nameRangeLo = -300, nameRangeHi = -201}
stripesBelowZero
  :: Int  -- ^ How many names a unit may declare.
  -> StripeLayout
stripesBelowZero size = StripeLayout $ \(StripeIndex i) ->
  let hi = negate (i * size) - 1
   in NameRange (hi - size + 1) hi

-- | Stripe @i@ is the @i@-th run of @size@ names at or above a base,
-- counting upwards, so stripe 0 is @[base .. base + size - 1]@.
--
-- >>> stripeRange (stripesAbove 0 100) (StripeIndex 1)
-- NameRange {nameRangeLo = 100, nameRangeHi = 199}
stripesAbove
  :: Int  -- ^ The base: the low end of stripe 0.
  -> Int  -- ^ How many names a unit may declare.
  -> StripeLayout
stripesAbove base size = StripeLayout $ \(StripeIndex i) ->
  let lo = base + i * size
   in NameRange lo (lo + size - 1)

-- | Which stripe each unit's declarations live in, by the unit's name.
--
-- Append-only: a name, once registered, keeps its stripe for the lifetime of
-- the registry, and the next stripe index is always the registry's size.
type Registry name = Map name StripeIndex

-- | The registry before any unit has ever been checked.
emptyRegistry :: Registry name
emptyRegistry = Map.empty

-- | How many units have been registered, which is also the next free stripe.
registrySize :: Registry name -> Int
registrySize = Map.size

-- | The stripe of a unit, assigning the next one on first use.
--
-- >>> let layout = stripesBelowZero 10
-- >>> let (r1, rangeA) = registerUnit layout "A" emptyRegistry
-- >>> rangeA
-- NameRange {nameRangeLo = -10, nameRangeHi = -1}
-- >>> snd (registerUnit layout "B" r1)
-- NameRange {nameRangeLo = -20, nameRangeHi = -11}
--
-- Registration is idempotent, which is the determinism a cache rests on:
--
-- >>> snd (registerUnit layout "A" r1) == rangeA
-- True
registerUnit
  :: Ord name
  => StripeLayout -> name -> Registry name -> (Registry name, NameRange)
registerUnit layout name registry = case Map.lookup name registry of
  Just i  -> (registry, stripeRange layout i)
  Nothing ->
    let i = StripeIndex (Map.size registry)
     in (Map.insert name i registry, stripeRange layout i)
