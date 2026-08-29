{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Deterministic stripe assignment for separately checked units.
--
-- Each unit of a module system allocates its top-level names inside its own
-- reservation (see "Control.Monad.Foil.Blocks"), and the assignment of
-- reservations has to be /deterministic/: a unit's declarations are numbered
-- @base@, @base + 1@, and so on in declaration order, whatever else is
-- checked around it. Determinism is what makes raw names cacheable, since a
-- unit checked today and a unit loaded tomorrow then agree name for name. It
-- is also what discharges the trust obligation of
-- 'Control.Monad.Foil.Blocks.checkExtScope'.
--
-- The registry is that assignment: an append-only map from unit names to
-- stripe indices, handing out the next index on first use. A build persists
-- it beside the build products, since a cached artifact survives a change
-- elsewhere in the build exactly when the assignment does not move.
--
-- Where the stripes lie on the raw-name line is a 'StripeLayout' and a
-- policy of the client. The library is region-agnostic, and the allocator
-- admits negative names.
module Control.Monad.Foil.Registry (
  -- * Stripe indices
  StripeIndex (..),
  -- * Layouts
  StripeSize (..),
  StripeLayout (..),
  stripesBelowZero,
  stripesAbove,
  -- * Local-region layouts
  RegionWidth (..),
  RegionsPerUnit (..),
  RegionLayout (..),
  regionsAbove,
  -- * The registry
  Registry,
  emptyRegistry,
  registrySize,
  registerUnit,
) where

import           Data.Binary                 (Binary)
import           Data.Map                    (Map)
import qualified Data.Map                    as Map

import           Control.Monad.Foil.Internal (NameRange (..), RawName)

-- $setup
-- >>> import Control.Monad.Foil.Internal

-- | A stripe's position in the registry: which run of names a unit draws
-- from. Its own type, so that a stripe index cannot be confused with a name,
-- a count, or an offset.
--
-- @since 0.4.0
newtype StripeIndex = StripeIndex Int
  deriving newtype (Eq, Ord, Show, Read, Binary)

-- | How many names a unit may declare: the width of every stripe a layout
-- hands out. Its own type, so that a size cannot be confused with a name, an
-- index, or a base.
--
-- @since 0.4.0
newtype StripeSize = StripeSize Int
  deriving newtype (Eq, Ord, Show, Read)

-- | Where stripe @i@ lies on the raw-name line.
--
-- The library does not choose: whether stripes descend below zero, ascend
-- from some base, or interleave with other reservations is a policy of the
-- client, and everything in "Control.Monad.Foil.Blocks" works from the
-- resulting 'NameRange's alone. A layout should give disjoint ranges to
-- distinct indices. Nothing checks this here, but
-- 'Control.Monad.Foil.Blocks.withDisjointUnion' refuses the overlap at the
-- point where it would do harm.
--
-- @since 0.4.0
newtype StripeLayout = StripeLayout
  { stripeRange :: StripeIndex -> NameRange
  }

-- | Stripe @i@ is the @i@-th run of @size@ names below zero, counting
-- downwards, so stripe 0 is @[-size .. -1]@. Within a stripe, allocation
-- still ascends (see 'Control.Monad.Foil.withFreshIn'), so declaration order
-- is ascending name order.
--
-- This layout leaves the whole non-negative range free for a client's local
-- names.
--
-- >>> stripeRange (stripesBelowZero (StripeSize 100)) (StripeIndex 0)
-- NameRange {nameRangeLo = -100, nameRangeHi = -1}
-- >>> stripeRange (stripesBelowZero (StripeSize 100)) (StripeIndex 2)
-- NameRange {nameRangeLo = -300, nameRangeHi = -201}
--
-- @since 0.4.0
stripesBelowZero :: StripeSize -> StripeLayout
stripesBelowZero (StripeSize size) = StripeLayout $ \(StripeIndex i) ->
  let hi = negate (i * size) - 1
   in NameRange (hi - size + 1) hi

-- | Stripe @i@ is the @i@-th run of @size@ names at or above a base,
-- counting upwards, so stripe 0 is @[base .. base + size - 1]@.
--
-- >>> stripeRange (stripesAbove 0 (StripeSize 100)) (StripeIndex 1)
-- NameRange {nameRangeLo = 100, nameRangeHi = 199}
--
-- @since 0.4.0
stripesAbove
  :: RawName     -- ^ The base: the low end of stripe 0.
  -> StripeSize
  -> StripeLayout
stripesAbove base (StripeSize size) = StripeLayout $ \(StripeIndex i) ->
  let lo = base + i * size
   in NameRange lo (lo + size - 1)

-- | Which stripe each unit's declarations live in, by the unit's name.
--
-- Append-only: a name, once registered, keeps its stripe for the lifetime of
-- the registry, and the next stripe index is always the registry's size.
--
-- @since 0.4.0
type Registry name = Map name StripeIndex

-- | The registry before any unit has ever been checked.
--
-- @since 0.4.0
emptyRegistry :: Registry name
emptyRegistry = Map.empty

-- | How many units have been registered, which is also the next free stripe.
--
-- @since 0.4.0
registrySize :: Registry name -> Int
registrySize = Map.size

-- | The stripe index of a unit, assigning the next one on first use.
--
-- Registration hands out the index and not a range. A unit's index
-- determines /every/ reservation derived for it: its stripe under a
-- 'StripeLayout', and its runs of local names under a 'RegionLayout'. The
-- layouts interpret the index, rather than being consulted here.
--
-- >>> let layout = stripesBelowZero (StripeSize 10)
-- >>> let (r1, iA) = registerUnit "A" emptyRegistry
-- >>> stripeRange layout iA
-- NameRange {nameRangeLo = -10, nameRangeHi = -1}
-- >>> stripeRange layout (snd (registerUnit "B" r1))
-- NameRange {nameRangeLo = -20, nameRangeHi = -11}
--
-- Registration is idempotent, which is the determinism a cache rests on:
--
-- >>> snd (registerUnit "A" r1) == iA
-- True
--
-- @since 0.4.0
registerUnit
  :: Ord name
  => name -> Registry name -> (Registry name, StripeIndex)
registerUnit name registry = case Map.lookup name registry of
  Just i  -> (registry, i)
  Nothing ->
    let i = StripeIndex (Map.size registry)
     in (Map.insert name i registry, i)

-- * Local-region layouts

-- | How far apart consecutive local-region floors sit within a unit's runs.
-- This is spacing, not a hard width: a run is open-ended above its floor,
-- and a scope-driven allocator would have to hold this many names /in scope
-- at once/ to reach the next floor.
--
-- @since 0.4.0
newtype RegionWidth = RegionWidth Int
  deriving newtype (Eq, Ord, Show, Read)

-- | How many runs of local names a unit may hold before its runs would
-- spill into the next unit's. A spill is not unsound for a client that
-- refreshes on clash. It only forfeits the disjointness described under
-- 'RegionLayout' for the runs past the cap.
--
-- @since 0.4.0
newtype RegionsPerUnit = RegionsPerUnit Int
  deriving newtype (Eq, Ord, Show, Read)

-- | Where a unit's runs of /local/ names lie: one open-ended region per
-- declaration (or command) of the unit, advanced with 'nextRegion' as the
-- unit's declarations are processed.
--
-- Stripes make a unit's top-level names disjoint from every other unit's,
-- and runs of local regions do the same for the names a checker invents
-- /inside/ a declaration. A term stored under one declaration then never
-- collides with another declaration's live locals when it is reopened, so a
-- refreshing substitution takes its no-rename fast path throughout.
--
-- The first run is derived from the unit's stripe index rather than from a
-- counter shared across units, so a unit's elaboration depends only on the
-- unit itself and editing a neighbour moves no name. That is the
-- determinism a cache rests on.
--
-- The trade-off is that local names carry large offsets. A client that
-- shows raw indices directly may prefer a single flat region, and accept
-- the transient renames instead.
--
-- @since 0.4.0
data RegionLayout = RegionLayout
  { firstRegionOf :: StripeIndex -> NameRange
    -- ^ The run of the unit's first declaration.
  , nextRegion    :: NameRange -> NameRange
    -- ^ The next declaration's run.
  }

-- | Runs ascending from a base: the unit with stripe index @i@ starts its
-- runs at @base + i * perUnit * width@, and each declaration's floor sits
-- @width@ above the previous one. The top of every run is open.
--
-- >>> let locals = regionsAbove 0 (RegionsPerUnit 0x10) (RegionWidth 0x100)
-- >>> nameRangeLo (firstRegionOf locals (StripeIndex 2))
-- 8192
-- >>> nameRangeLo (nextRegion locals (firstRegionOf locals (StripeIndex 2)))
-- 8448
--
-- @since 0.4.0
regionsAbove :: RawName -> RegionsPerUnit -> RegionWidth -> RegionLayout
regionsAbove base (RegionsPerUnit perUnit) (RegionWidth w) = RegionLayout
  { firstRegionOf = \(StripeIndex i) ->
      NameRange (base + i * perUnit * w) maxBound
  , nextRegion = \(NameRange lo _) -> NameRange (lo + w) maxBound
  }
