{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Reserved name blocks, and linking of independently checked scopes.
--
-- Each unit of a module system allocates its names inside its own
-- reservation (a 'NameRange', via 'withFreshIn'), so that units checked
-- independently can be linked afterwards without renaming. 'ExtWithin' is
-- the evidence for that: scope @l@ extends scope @n@ only within a set of
-- reserved ranges. Note that the ranges bound the /extension/ and not the
-- scope, so the names of @n@ itself (typically, a unit's imports) may lie
-- anywhere.
--
-- Two units that extend a common scope within disjoint reservations have
-- disjoint extensions. 'withDisjointUnion' links them by comparing the
-- reservations rather than the scopes, and hands the continuation the
-- extension evidence for both sides, a 'ScopeUnion' witness that the result
-- is the union and nothing more, and the union's own evidence, so that a
-- linked unit is itself linkable. Evidence composes along a chain of units
-- with 'composeExtWithin'. To link more than two units, or to re-attach a
-- unit loaded from a cache, rebuild the union scope and mint the evidence
-- again with 'checkExtScope' and 'checkScopeUnion'.
--
-- 'checkExtScope' and 'checkScopeUnion' are a trust boundary. They compare
-- raw names across independently built scopes, which is meaningful only
-- under a deterministic reservation policy. Everything else in this module
-- either tests what it claims or constructs it.
module Control.Monad.Foil.Blocks (
  -- * Extension-within-a-range evidence
  ExtWithin,
  extWithinRanges,
  extWithinRefl,
  extWithinStep,
  composeExtWithin,
  -- * Blocks in use
  Block,
  beginBlock,
  resumeBlock,
  blockRange,
  blockExt,
  withFreshInBlock,
  -- * Bulk extension of a scope by a range
  withExtendScopeRange,
  -- * Linking
  ScopeUnion,
  withDisjointUnion,
  checkScopeUnion,
  checkExtScope,
  unionNameMaps,
) where

import           Data.List                   (sortOn)
import qualified Data.IntMap                 as IntMap
import qualified Data.IntSet                 as IntSet
import           Unsafe.Coerce               (unsafeCoerce)

import           Control.Monad.Foil.Internal

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XFlexibleContexts
-- >>> import Control.Monad.Foil.Internal

-- | Evidence that scope @l@ extends scope @n@ only within a set of reserved
-- ranges: every name of @l@ that is not a name of @n@ lies inside one of
-- them.
--
-- The evidence is built alongside allocation, with 'extWithinRefl' at the
-- start of a unit and 'extWithinStep' at each binder, and composes along a
-- chain of scopes with 'composeExtWithin'. Its runtime content is the
-- ranges, sorted and disjoint.
data ExtWithin (n :: S) (l :: S) = UnsafeExtWithin [NameRange]

-- | The reservations an 'ExtWithin' is evidence about: sorted, disjoint,
-- adjacent ranges coalesced, empty ones dropped.
extWithinRanges :: ExtWithin n l -> [NameRange]
extWithinRanges (UnsafeExtWithin ranges) = ranges

-- | A scope extends itself within any range: the extension is empty.
--
-- Note that this does /not/ say the range is disjoint from the scope. It is
-- 'withExtendScopeRange' that checks that, because it allocates blindly.
extWithinRefl :: NameRange -> ExtWithin n n
extWithinRefl range = UnsafeExtWithin (normaliseRanges [range])

-- | Extend the evidence across one more binder, if its name lies inside one
-- of the ranges. One membership test per range.
--
-- A binder allocated by 'withFreshIn' at one of these ranges always passes.
-- A binder allocated elsewhere, by 'withFresh' or 'withRefreshed', is
-- rejected with 'Nothing' unless it happens to land inside them, so the
-- evidence cannot be extended past a name that escapes the reservations.
--
-- >>> let range = NameRange 100 199
-- >>> withFreshIn range emptyScope (\b -> fmap extWithinRanges (extWithinStep b (extWithinRefl range)))
-- Just [NameRange {nameRangeLo = 100, nameRangeHi = 199}]
extWithinStep :: NameBinder l l' -> ExtWithin n l -> Maybe (ExtWithin n l')
extWithinStep binder (UnsafeExtWithin ranges)
  | any (\(NameRange lo hi) -> lo <= x && x <= hi) ranges = Just (UnsafeExtWithin ranges)
  | otherwise = Nothing
  where
    x = nameId (nameOf binder)

-- | Compose evidence along a chain of scopes: if @m@ extends @n@ only within
-- one set of ranges and @l@ extends @m@ only within another, then @l@
-- extends @n@ only within their union.
--
-- The bound is the union of the two sets and not their hull, so a
-- reservation lying between them stays linkable. Adjacent ranges are
-- coalesced, so a chain of units with consecutive stripes collapses back to
-- a single range.
--
-- >>> extWithinRanges (composeExtWithin (extWithinRefl (NameRange 0 9)) (extWithinRefl (NameRange 30 39)))
-- [NameRange {nameRangeLo = 0, nameRangeHi = 9},NameRange {nameRangeLo = 30, nameRangeHi = 39}]
-- >>> extWithinRanges (composeExtWithin (extWithinRefl (NameRange 0 9)) (extWithinRefl (NameRange 10 19)))
-- [NameRange {nameRangeLo = 0, nameRangeHi = 19}]
composeExtWithin :: ExtWithin n m -> ExtWithin m l -> ExtWithin n l
composeExtWithin (UnsafeExtWithin rs1) (UnsafeExtWithin rs2) =
  UnsafeExtWithin (normaliseRanges (rs1 <> rs2))

-- | Sort ranges, drop empty ones, and coalesce overlapping or adjacent ones.
normaliseRanges :: [NameRange] -> [NameRange]
normaliseRanges = go . sortOn nameRangeLo . filter nonEmpty
  where
    nonEmpty (NameRange lo hi) = lo <= hi
    go (NameRange lo1 hi1 : r2@(NameRange lo2 hi2) : rs)
      | lo2 <= hi1                      = go (NameRange lo1 (max hi1 hi2) : rs)
      | hi1 /= maxBound, lo2 == hi1 + 1 = go (NameRange lo1 hi2 : rs)
      | otherwise = NameRange lo1 hi1 : go (r2 : rs)
    go rs = rs

-- | Whether two sorted sets of disjoint ranges share a name. One sweep.
rangeSetsOverlap :: [NameRange] -> [NameRange] -> Bool
rangeSetsOverlap (r1@(NameRange lo1 hi1) : rs1) (r2@(NameRange lo2 hi2) : rs2)
  | hi1 < lo2 = rangeSetsOverlap rs1 (r2 : rs2)
  | hi2 < lo1 = rangeSetsOverlap (r1 : rs1) rs2
  | otherwise = True
rangeSetsOverlap _ _ = False

-- | A reservation in use: the range fresh names are allocated from, paired
-- with the evidence that everything allocated since the base scope @c@ lies
-- within the unit's ranges.
--
-- The allocation range is always among the evidence's ranges, so stepping
-- the evidence at a freshly allocated name cannot fail and 'withFreshInBlock'
-- is total. The two components are not redundant: the evidence is a
-- normalised set bounding the whole extension, and once units are composed
-- the range to allocate from can no longer be read off it.
data Block (c :: S) (l :: S) = UnsafeBlock !NameRange (ExtWithin c l)

-- | Start a unit: no names allocated yet, so the evidence is trivial.
beginBlock :: NameRange -> Block c c
beginBlock range = UnsafeBlock range (extWithinRefl range)

-- | Resume allocating from a range once the evidence has grown past what a
-- 'Block' tracked by itself, after composing in a loaded unit's evidence
-- with 'composeExtWithin'. This is what lets an interactive unit keep
-- allocating in its own reservation over the enlarged scope.
--
-- The allocation range must lie inside one of the evidence's ranges. The
-- ranges are normalised, so covering is containment in a single one, and
-- 'Nothing' says the range is not covered.
--
-- >>> let grown = composeExtWithin (extWithinRefl (NameRange 0 9)) (extWithinRefl (NameRange 10 19))
-- >>> fmap blockRange (resumeBlock (NameRange 0 9) grown)
-- Just (NameRange {nameRangeLo = 0, nameRangeHi = 9})
-- >>> fmap blockRange (resumeBlock (NameRange 30 39) grown)
-- Nothing
resumeBlock :: NameRange -> ExtWithin c l -> Maybe (Block c l)
resumeBlock range@(NameRange lo hi) ext
  | lo > hi = Nothing
  | any covers (extWithinRanges ext) = Just (UnsafeBlock range ext)
  | otherwise = Nothing
  where
    covers (NameRange lo' hi') = lo' <= lo && hi <= hi'

-- | The range 'withFreshInBlock' allocates from.
blockRange :: Block c l -> NameRange
blockRange (UnsafeBlock range _) = range

-- | The evidence accumulated so far: what a finished unit hands to
-- 'withDisjointUnion', or to 'composeExtWithin' for the next unit of a
-- chain.
blockExt :: Block c l -> ExtWithin c l
blockExt (UnsafeBlock _ ext) = ext

-- | Allocate a fresh name in the block's range, stepping the evidence in
-- the same motion. Fails with 'error' only on an exhausted range, exactly
-- as 'withFreshIn' does.
--
-- >>> withFreshInBlock (beginBlock (NameRange 7 9)) emptyScope (\b block -> (nameId (nameOf b), extWithinRanges (blockExt block)))
-- (7,[NameRange {nameRangeLo = 7, nameRangeHi = 9}])
withFreshInBlock
  :: Distinct l
  => Block c l  -- ^ The block to allocate from.
  -> Scope l    -- ^ The ambient scope.
  -> (forall l'. DExt l l' => NameBinder l l' -> Block c l' -> r)
  -> r
withFreshInBlock (UnsafeBlock range ext) scope cont =
  withFreshIn range scope $ \binder ->
    case extWithinStep binder ext of
      Just ext' -> cont binder (UnsafeBlock range ext')
      Nothing   -> error "impossible: withFreshIn allocated outside its own range"

-- | Extend a scope with the first @k@ names of a range, in one step.
--
-- This is the bulk form of a unit's allocation, for loading a cached unit
-- whose extension is known to be @k@ consecutive names, or for pre-allocating
-- a unit's names before checking its bodies. The range part of the scope must
-- be empty, which is checked, so the extension is fresh by construction.
-- 'Nothing' reports an occupied range, and also a range with fewer than @k@
-- names.
--
-- The continuation receives the extended scope, the binders in ascending
-- order (for extending a 'NameMap' in the same step), and the 'ExtWithin'
-- evidence. The scope extension is a dense 'IntSet.fromRange', \(O(k/W)\).
--
-- >>> withExtendScopeRange emptyScope (NameRange 100 199) 3 (\_ binders _ -> rawNameBinderList binders)
-- Just [100,101,102]
withExtendScopeRange
  :: forall c r. Distinct c
  => Scope c      -- ^ The scope to extend (typically, a unit's imports).
  -> NameRange    -- ^ The unit's reservation.
  -> Int          -- ^ How many names to allocate.
  -> (forall n. DExt c n => Scope n -> NameBinderList c n -> ExtWithin c n -> r)
  -> Maybe r
withExtendScopeRange (UnsafeScope scope) range@(NameRange lo hi) k cont
  | k < 0                        = Nothing
  | rangeOccupied                = Nothing
  | toInteger k > rangeCapacity  = Nothing
  | otherwise =
      Just (unsafeExtendedWithin (UnsafeScope scope') binders (UnsafeExtWithin (normaliseRanges [range])) cont)
  where
    rangeOccupied = case IntSet.lookupGE lo scope of
      Just y  -> y <= hi
      Nothing -> False
    rangeCapacity = max 0 (toInteger hi - toInteger lo + 1)
    scope'
      | k == 0    = scope
      | otherwise = IntSet.union scope (IntSet.fromRange (lo, lo + (k - 1)))
    binders :: forall n. NameBinderList c n
    binders = go (if k == 0 then [] else [lo .. lo + (k - 1)])
      where
        go :: forall m m'. [RawName] -> NameBinderList m m'
        go []       = unsafeCoerce NameBinderListEmpty
        go (x : xs) = NameBinderListCons (UnsafeNameBinder (UnsafeName x)) (go xs)

-- | Unsafely mint the evidence for an extension built by this module.
--
-- Sound when the scope really is the given base extended by the binders, and
-- the binders' names lie inside the evidence's range and are fresh in the
-- base. The callers here check or construct all three.
unsafeExtendedWithin
  :: forall c n r
   . Scope n -> NameBinderList c n -> ExtWithin c n
  -> (DExt c n => Scope n -> NameBinderList c n -> ExtWithin c n -> r)
  -> r
unsafeExtendedWithin scope binders ext cont =
  case unsafeDistinct @n of
    Distinct -> case unsafeExt @c @n of
      Ext -> cont scope binders ext

-- | Link two scopes that extend a common scope @c@ within their respective
-- reservations. The evidence check is one sweep over the two range sets;
-- the scope union is one 'IntSet.union'.
--
-- 'Nothing' when the two range sets overlap. The test is soundness and not
-- an optimisation. The extensions @n \\ c@ and @m \\ c@ lie inside their
-- respective range sets, so their disjointness is what guarantees that no
-- raw name denotes two different variables in the union. The names the two
-- scopes share are exactly the names of @c@, identified rather than renamed
-- apart, which is what linking two units over a common import must do.
--
-- The continuation receives both extension facts at once, a 'ScopeUnion'
-- witness (which 'unionNameMaps' requires), and the union's own 'ExtWithin',
-- so that a linked unit is itself linkable and a whole build folds through
-- this one function. It also receives @'Ext' c k@, which a caller cannot
-- derive on the spot.
withDisjointUnion
  :: forall c n m r. (Distinct n, Distinct m)
  => ExtWithin c n  -- ^ Evidence for the first unit.
  -> ExtWithin c m  -- ^ Evidence for the second unit.
  -> Scope n        -- ^ The first unit's scope.
  -> Scope m        -- ^ The second unit's scope.
  -> (forall k. (Ext n k, Ext m k, Ext c k, Distinct k)
        => Scope k -> ScopeUnion n m k -> ExtWithin c k -> r)
  -> Maybe r
withDisjointUnion (UnsafeExtWithin rs1) (UnsafeExtWithin rs2) (UnsafeScope s1) (UnsafeScope s2) cont
  | rangeSetsOverlap rs1 rs2 = Nothing
  | otherwise           = Just (unsafeUnion (UnsafeScope (IntSet.union s1 s2)))
  where
    unsafeUnion :: forall k. Scope k -> r
    unsafeUnion scope =
      case unsafeDistinct @k of
        Distinct -> case unsafeExt @n @k of
          Ext -> case unsafeExt @m @k of
            Ext -> case unsafeExt @c @k of
              -- Each side extends the base within its own ranges, so the
              -- names of c are in n and in m, hence in the union. This is
              -- handed to the continuation as a given because deriving it
              -- from Ext c n and Ext n k leaves the solver two candidate
              -- paths and it commits to neither.
              Ext -> cont scope UnsafeScopeUnion
                          (UnsafeExtWithin (normaliseRanges (rs1 <> rs2)))

-- | Evidence that scope @k@ is /precisely/ the union of scopes @n@ and @m@:
-- every name of @n@ and of @m@ is a name of @k@, and nothing else is.
--
-- The extension constraints @('Ext' n k, 'Ext' m k)@ state only the first
-- half, since a strict superset of the union satisfies them too. The second
-- half is what totality of a merged 'NameMap' rests on, so 'unionNameMaps'
-- demands this witness. It comes from 'withDisjointUnion', which builds the
-- union, or from 'checkScopeUnion', which tests for it.
data ScopeUnion (n :: S) (m :: S) (k :: S) = UnsafeScopeUnion

-- | Test that a scope is precisely the union of two others, and produce the
-- witness if so. \(O(n+m)\).
--
-- This is the union witness for the re-attachment path, where the union
-- scope was rebuilt rather than handed down by 'withDisjointUnion'. Like
-- 'checkExtScope', it compares raw names across independently built scopes,
-- and is meaningful only under a deterministic reservation policy.
checkScopeUnion :: Scope n -> Scope m -> Scope k -> Maybe (ScopeUnion n m k)
checkScopeUnion (UnsafeScope s1) (UnsafeScope s2) (UnsafeScope s3)
  | IntSet.union s1 s2 == s3 = Just UnsafeScopeUnion
  | otherwise                = Nothing

-- | Test that every name of one scope is a name of another, and mint the
-- extension evidence if so. \(O(n+m)\) ('IntSet.isSubsetOf').
--
-- __This is a trust boundary.__ The test compares raw names, and raw names
-- from independently built scopes need not mean the same variable. The type
-- system tracks meaning through binders, and this function goes around it
-- deliberately, to re-attach a scope built elsewhere: in an earlier run, in
-- a cache, or in a parallel session. It is sound only under the external
-- discipline that a raw name has one global meaning, which a deterministic
-- reservation policy provides. Nothing here checks that discipline, and the
-- caller's allocator is what has to.
checkExtScope :: Scope n -> Scope l -> Maybe (ExtEvidence n l)
checkExtScope (UnsafeScope s1) (UnsafeScope s2)
  | s1 `IntSet.isSubsetOf` s2 = Just unsafeExt
  | otherwise                 = Nothing

-- | Union of two total maps into a map on the union of their scopes.
-- Left-biased, like 'IntMap.union'.
--
-- The witness is what makes the result total on @k@. The inputs are total on
-- @n@ and @m@, and 'ScopeUnion' says that @k@ holds their names and no
-- others. (It also determines @k@, which an extension constraint alone would
-- leave open.)
--
-- What no witness can say is that the two maps agree on the names their
-- scopes share. Linked units agree there when the shared part comes from the
-- same checked imports, and the left bias then only ever chooses between
-- equal entries.
unionNameMaps :: ScopeUnion n m k -> NameMap n a -> NameMap m a -> NameMap k a
unionNameMaps UnsafeScopeUnion (NameMap m1) (NameMap m2) = NameMap (IntMap.union m1 m2)
