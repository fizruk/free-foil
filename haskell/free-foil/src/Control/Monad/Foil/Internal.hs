{-# OPTIONS_GHC -Wno-missing-methods #-}  -- disabled to avoid overlapping type instances
{-# OPTIONS_GHC -Wno-overlapping-patterns -Wno-inaccessible-code #-}  -- disabled because I think GHC is wrong
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE DefaultSignatures          #-}
-- | Main definitions of the foil that can be
-- reused for specific implementations.
-- This is an internal module, so it also contains implementation details of the foil.
--
-- The original description of this approach
-- is described in the IFL 2022 paper by Maclaurin, Radul, and Paszke
-- [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224).
-- This module also introduces 'CoSinkable' class,
-- generalizing handling of patterns, as described in
-- [«Free Foil: Generating Efficient and Scope-Safe Abstract Syntax»](https://arxiv.org/abs/2405.16384).
--
-- Since the representation of scopes and substitutions
-- is either @IntMap@ or @IntSet@, many of the operations
-- have a worst-case complexity of \(O(\min(n,W))\).
-- This means that the operation can become linear in the size of the scope \(n\) with a
-- maximum of \(W\), the number of bits in an 'Int' (32 or 64).
module Control.Monad.Foil.Internal where

import           Control.DeepSeq    (NFData (..))
import           Data.Bifunctor
import           Data.Coerce        (coerce)
import           Data.Functor.Compose (Compose (..))
import           Data.Bifunctor.Tannen (Tannen (..))
import           Data.IntMap
import qualified Data.IntMap        as IntMap
import qualified Data.Map
import           Data.IntSet
import qualified Data.IntSet        as IntSet
import           Data.Kind          (Type)
import qualified Data.Type.Equality as Type
import           Generics.Kind
import           Unsafe.Coerce

import Control.Monad.Foil.Internal.ValidNameBinders

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XFlexibleContexts
-- >>> :set -Wno-simplifiable-class-constraints
-- >>> import qualified Data.Map as Map
-- >>> import qualified Data.IntSet as IntSet
-- >>> import Data.Bifunctor.Tannen

-- * Safe types and operations

-- | 'S' is a data kind of scope indices.
--
-- @since 0.0.1
data S
  = VoidS -- ^ 'VoidS' is the only explicit scope available to the users, representing an empty scope.
          -- All other scopes are represented with type variables,
          -- bound in rank-2 polymophic functions like 'withFreshBinder'.

-- | A safe scope, indexed by a type-level scope index @n@.
--
-- @since 0.0.1
newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData

-- | A name in a safe scope, indexed by a type-level scope index @n@.
--
-- @since 0.0.1
newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord, Show)

-- | Convert 'Name' into an identifier.
-- This may be useful for printing and debugging.
--
-- @since 0.0.1
nameId :: Name l -> Id
nameId (UnsafeName i) = i

-- | A name binder is a name that extends scope @n@ to a (larger) scope @l@.
--
-- @since 0.0.1
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord, Show)

-- | An empty scope (without any names).
--
-- @since 0.0.1
emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

-- | A runtime check for potential name capture.
--
-- @since 0.0.1
member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

-- ** Extending scopes

-- | \(O(\min(n,W))\).
-- Extend a scope with one name (safely).
-- Note that as long as the foil is used as intended,
-- the name binder is guaranteed to introduce a name
-- that does not appear in the initial scope.
--
-- @since 0.0.1
{-# INLINABLE extendScope #-}
extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName name)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert name scope)

-- | Extend scope with variables inside a pattern.
-- This is a more flexible version of 'extendScope'.
--
-- @since 0.0.1
{-# INLINABLE extendScopePattern #-}
extendScopePattern
  :: (Distinct n, CoSinkable pattern)
  => pattern n l -> Scope n -> Scope l
extendScopePattern pat scope = withPattern
  (\_scope' binder k ->
    unsafeAssertFresh binder $ \binder' ->
      k (ExtendScope (extendScope binder)) binder')
  idExtendScope
  compExtendScope
  scope
  pat
  (\(ExtendScope extend) _ _ -> extend scope)

-- | Auxiliary data structure for scope extension. Used in 'extendScopePattern'.
--
-- @since 0.1.0
newtype ExtendScope n l (o :: S) (o' :: S) = ExtendScope (Scope n -> Scope l)

-- | Identity scope extension (no extension).
--
-- @since 0.1.0
idExtendScope :: ExtendScope n n o o'
idExtendScope = ExtendScope id

-- | Compose scope extensions.
--
-- @since 0.1.0
compExtendScope
  :: ExtendScope n i o o'
  -> ExtendScope i l o' o''
  -> ExtendScope n l o o''
compExtendScope (ExtendScope f) (ExtendScope g)
  = ExtendScope (g . f)

-- ** Collecting new names

-- | Extract name from a name binder.
--
-- @since 0.0.1
nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

-- | Extract names from a pattern.
-- This is a more flexible version of 'nameOf'.
--
-- @since 0.1.0
namesOfPattern
  :: forall pattern n l. (Distinct n, CoSinkable pattern) => pattern n l -> [Name l]
namesOfPattern pat = withPattern @_ @n
  (\_scope' binder k ->
    unsafeAssertFresh binder $ \binder' ->
      k (NamesOf [nameOf binder]) binder')
  idNamesOf compNamesOf (error "impossible") pat
  (\(NamesOf names) _ _ -> names)

-- | Auxiliary structure collecting names in scope @l@ that extend scope @n@.
-- Used in 'namesOfPattern'.
--
-- @since 0.1.0
newtype NamesOf (n :: S) l (o :: S) (o' :: S) = NamesOf [Name l]

-- | Empty list of names in scope @n@.
--
-- @since 0.1.0
idNamesOf :: NamesOf n n o o'
idNamesOf = NamesOf []

-- | Concatenation of names, resulting in a list of names in @l@ that extend scope @n@.
--
-- @since 0.1.0
compNamesOf :: NamesOf n i o o' -> NamesOf i l o' o'' -> NamesOf n l o o''
compNamesOf (NamesOf xs) (NamesOf ys) =
  NamesOf (coerce xs ++ ys)

-- ** Refreshing binders

-- | Allocate a fresh binder for a given scope.
--
-- @since 0.0.1
{-# INLINABLE withFreshBinder #-}
withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r) -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

-- | Safely produce a fresh name binder with respect to a given scope.
--
-- @since 0.0.1
{-# INLINABLE withFresh #-}
withFresh
  :: Distinct n => Scope n
  -> (forall l. DExt n l => NameBinder n l -> r) -> r
withFresh scope cont = withFreshBinder scope (`unsafeAssertFresh` cont)

-- | Safely produce a fresh name binder, allocated within a given range.
--
-- The binder is fresh with respect to the whole ambient scope, not merely to
-- its part inside the range. Indeed, the allocated name lies in the range and
-- is greater than every scope member there, while a scope member outside the
-- range cannot be equal to a name inside it (see 'rawFreshNameIn'). Thus the
-- usual freshness evidence applies, and no invariant beyond the scope itself
-- is required.
--
-- This is the primitive behind allocation policies such as per-module name
-- blocks: reserve disjoint ranges for independently checked units, and the
-- names allocated for them can never collide.
--
-- Fails with 'error' when the range is exhausted. Use 'tryWithFreshIn' to
-- handle exhaustion instead.
--
-- >>> withFreshIn (NameRange 100 199) emptyScope (nameId . nameOf)
-- 100
--
-- @since 0.4.0
withFreshIn
  :: Distinct n
  => NameRange  -- ^ The reservation to allocate from.
  -> Scope n    -- ^ The ambient scope.
  -> (forall l. DExt n l => NameBinder n l -> r) -> r
withFreshIn range scope cont =
  case tryWithFreshIn range scope cont of
    Just r  -> r
    Nothing -> error ("withFreshIn: exhausted " <> show range)

-- | A version of 'withFreshIn' that reports an exhausted range with 'Nothing'
-- instead of failing. A driver that hands out ranges can then report which
-- unit ran out of its reservation.
--
-- @since 0.4.0
tryWithFreshIn
  :: Distinct n
  => NameRange  -- ^ The reservation to allocate from.
  -> Scope n    -- ^ The ambient scope.
  -> (forall l. DExt n l => NameBinder n l -> r) -> Maybe r
tryWithFreshIn range (UnsafeScope rawScope) cont =
  case rawFreshNameIn range rawScope of
    Nothing   -> Nothing
    Just name -> Just (unsafeAssertFresh (UnsafeNameBinder (UnsafeName name)) cont)

-- | Rename a given pattern into a fresh version of it to extend a given scope.
--
-- This is similar to 'withRefreshedPattern', except here renaming always takes place.
--
-- @since 0.1.0
withFreshPattern
  :: (Distinct o, CoSinkable pattern, Sinkable e, InjectName e)
  => Scope o      -- ^ Ambient scope.
  -> pattern n l  -- ^ Pattern to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => (Substitution e n o -> Substitution e l o') -> pattern o o' -> Scope o' -> r)
  -- ^ Continuation, accepting the refreshed pattern and the extended scope.
  -> r
withFreshPattern scope pattern cont = withPattern
  (\scope' binder f -> withFresh scope'
    (\binder' -> f (WithRefreshedPattern (\subst -> addRename (sink subst) binder (nameOf binder'))) binder'))
  idWithRefreshedPattern
  compWithRefreshedPattern
  scope
  pattern
  (\(WithRefreshedPattern f) pattern' scope' -> cont f pattern' scope')

-- | Safely rename (if necessary) a given name to extend a given scope.
-- This is similar to 'withFresh', except if the name does not clash with
-- the scope, it can be used immediately, without renaming.
--
-- @since 0.0.1
{-# INLINABLE withRefreshed #-}
withRefreshed
  :: Distinct o
  => Scope o    -- ^ Ambient scope.
  -> Name i     -- ^ Name to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => NameBinder o o' -> r)
  -- ^ Continuation, accepting the refreshed name.
  -> r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName rawName) cont
  | IntSet.member rawName rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

-- | A version of 'withRefreshed' that allocates the replacement name within
-- a given range when the candidate is taken. A client that reserves regions
-- of the raw-name line (per-module stripes, a region for locals) uses this
-- so that a rename cannot stray into someone else's reservation.
--
-- @since 0.4.0
withRefreshedIn
  :: Distinct o
  => NameRange  -- ^ The reservation to allocate a replacement from.
  -> Scope o    -- ^ Ambient scope.
  -> Name i     -- ^ Name to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => NameBinder o o' -> r)
  -- ^ Continuation, accepting the refreshed name.
  -> r
withRefreshedIn range scope@(UnsafeScope rawScope) name@(UnsafeName rawName) cont
  | IntSet.member rawName rawScope = withFreshIn range scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

-- | Safely rename (if necessary) a given pattern to extend a given scope.
-- This is similar to 'withFreshPattern', except if a name in the pattern
-- does not clash with the scope, it can be used immediately, without renaming.
--
-- This is a more general version of 'withRefreshed'.
--
-- The continuation also receives the scope extended with the refreshed
-- pattern: the traversal computes it along the way, so the caller does not
-- recompute it with 'extendScopePattern' (a second traversal of the same
-- pattern). The same holds for 'withFreshPattern' and 'withRefreshedPattern''.
--
-- Note that there is deliberately no fast path for the case when /every/ binder
-- of the pattern is already fresh in the ambient scope. It is tempting to test
-- all binders at once and, when none clashes, hand the continuation @sink@
-- instead of a renaming composed per binder. That would be unsound.
--
-- Even when a binder is not renamed, the per-binder step is not the identity:
-- 'addRename' /deletes/ the name from the substitution, which is how the binder
-- shadows an outer binding of the same raw name. For skipping that delete to be
-- harmless we would need the substitution's domain to avoid the pattern's binder
-- names, but the substitution's domain lives in the pattern's own scope @n@,
-- while freshness is tested against the unrelated ambient scope @o@.
--
-- The two can indeed disagree, because 'sink' is a coercion and does not
-- rename: a term built in a small scope keeps its binder names when it is
-- placed in a larger one, so a binder can share a raw name with its own
-- enclosing scope. Ordinary evaluation produces such terms, with a @λ x1@
-- nested inside another @λ x1@. Handing such a caller @sink@ would apply its
-- substitution to a name the pattern binds, which is to say capture the bound
-- variable.
--
-- @since 0.0.1
{-# INLINABLE withRefreshedPattern #-}
withRefreshedPattern
  :: (Distinct o, CoSinkable pattern, Sinkable e, InjectName e)
  => Scope o      -- ^ Ambient scope.
  -> pattern n l  -- ^ Pattern to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => (Substitution e n o -> Substitution e l o') -> pattern o o' -> Scope o' -> r)
  -- ^ Continuation, accepting the refreshed pattern and the extended scope.
  -> r
withRefreshedPattern scope pattern cont = withPattern
  (\scope' binder f -> withRefreshed scope' (nameOf binder)
    (\binder' -> f (WithRefreshedPattern (\subst -> addRename (sink subst) binder (nameOf binder'))) binder'))
  idWithRefreshedPattern
  compWithRefreshedPattern
  scope
  pattern
  (\(WithRefreshedPattern f) pattern' scope' -> cont f pattern' scope')

-- | Refresh (if needed) bound variables introduced in a pattern.
--
-- This is a version of 'withRefreshedPattern' that uses functional renamings instead of 'Substitution'.
--
-- Like 'withRefreshedPattern', this has no all-binders-already-fresh fast path,
-- and for the same reason. Here shadowing is handled by 'unsinkName' rather than
-- by a delete: a name the pattern binds is routed to 'injectName' and never
-- reaches the caller's renaming, whether or not the binder was refreshed.
--
-- @since 0.1.0
withRefreshedPattern'
  :: (CoSinkable pattern, Distinct o, InjectName e, Sinkable e)
  => Scope o
  -> pattern n l
  -> (forall o'. DExt o o' => ((Name n -> e o) -> Name l -> e o') -> pattern o o' -> Scope o' -> r) -> r
withRefreshedPattern' scope pattern cont = withPattern
  (\scope' binder f -> withRefreshed scope' (nameOf binder)
    (\binder' ->
      let k subst name = case unsinkName binder name of
              Nothing    -> injectName (nameOf binder')
              Just name' -> sink (subst name')
       in f (WithRefreshedPattern' k) binder'))
  idWithRefreshedPattern'
  compWithRefreshedPattern'
  scope
  pattern
  (\(WithRefreshedPattern' f) pattern' scope' -> cont f pattern' scope')

-- | Unsafely declare that a given name (binder)
-- is already fresh in any scope @n'@.
--
-- @since 0.0.1
{-# INLINABLE unsafeAssertFresh #-}
unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

-- | Auxiliary structure to accumulate substitution extensions
-- produced when refreshing a pattern.
-- Used in 'withRefreshedPattern' and 'withFreshPattern'.
--
-- @since 0.1.0
newtype WithRefreshedPattern e n l o o' = WithRefreshedPattern (Substitution e n o -> Substitution e l o')

-- | Trivial substitution (coercion via 'sink').
--
-- @since 0.1.0
idWithRefreshedPattern :: (Sinkable e, DExt o o') => WithRefreshedPattern e n n o o'
idWithRefreshedPattern = WithRefreshedPattern sink

-- | Composition of substitution extensions.
--
-- @since 0.1.0
compWithRefreshedPattern
  :: (DExt o o', DExt o' o'')
  => WithRefreshedPattern e n i o o'
  -> WithRefreshedPattern e i l o' o''
  -> WithRefreshedPattern e n l o o''
compWithRefreshedPattern (WithRefreshedPattern f) (WithRefreshedPattern g) =
  WithRefreshedPattern (g . f)

-- | Auxiliary structure to accumulate substitution extensions
-- and the extended scope produced when refreshing a pattern.
-- Similar to 'WithRefreshedPattern', except here substitutions are represented as functions.
-- Used in 'withRefreshedPattern''.
--
-- @since 0.1.0
newtype WithRefreshedPattern' e n l (o :: S) (o' :: S) = WithRefreshedPattern' ((Name n -> e o) -> Name l -> e o')

-- | Trivial substitution extension (coercion via 'sink').
--
-- @since 0.1.0
idWithRefreshedPattern' :: (Sinkable e, DExt o o') => WithRefreshedPattern' e n n o o'
idWithRefreshedPattern' = WithRefreshedPattern' (\f n -> sink (f n))

-- | Composition of substitution extensions.
--
-- @since 0.1.0
compWithRefreshedPattern'
  :: (DExt o o', DExt o' o'')
  => WithRefreshedPattern' e n i o o'
  -> WithRefreshedPattern' e i l o' o''
  -> WithRefreshedPattern' e n l o o''
compWithRefreshedPattern' (WithRefreshedPattern' f) (WithRefreshedPattern' g) =
  WithRefreshedPattern' (g . f)

-- ** Extracting proofs from binders and patterns

-- | Evidence that scope @n@ contains distinct names.
--
-- @since 0.0.1
data DistinctEvidence (n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

-- | Evidence that scope @l@ extends scope @n@.
--
-- @since 0.0.1
data ExtEvidence (n :: S) (l :: S) where
  Ext :: Ext n l => ExtEvidence n l

-- | A distinct scope extended with a 'NameBinder' is also distinct.
--
-- @since 0.0.1
assertDistinct :: (Distinct n, CoSinkable pattern) => pattern n l -> DistinctEvidence l
assertDistinct _ = unsafeDistinct

-- | A distinct scope extended with a 'NameBinder' is also distinct.
--
-- @since 0.0.3
assertExt :: CoSinkable pattern => pattern n l -> ExtEvidence n l
assertExt _ = unsafeExt

-- | Unsafely declare that scope @n@ is distinct.
-- Used in 'unsafeAssertFresh'.
--
-- @since 0.0.1
unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

-- | Unsafely declare that scope @l@ extends scope @n@.
-- Used in 'unsafeAssertFresh'.
--
-- @since 0.0.1
unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

-- ** Unsinking names

-- | Try coercing the name back to the (smaller) scope,
-- given a binder that extends that scope.
--
-- @since 0.0.1
unsinkName :: NameBinder n l -> Name l -> Maybe (Name n)
unsinkName binder name@(UnsafeName raw)
  | nameOf binder == name = Nothing
  | otherwise = Just (UnsafeName raw)

-- | Check if a name in the extended context
-- is introduced in a pattern or comes from the outer scope @n@.
--
-- This is a generalization of 'unsinkName'.
--
-- @since 0.1.0
unsinkNamePattern
  :: forall pattern n l. (Distinct n, CoSinkable pattern)
  => pattern n l -> Name l -> Maybe (Name n)
unsinkNamePattern pat = withPattern @_ @n
  (\_scope' binder k ->
      unsafeAssertFresh binder $ \binder' ->
        k (UnsinkName (unsinkName binder)) binder')
  idUnsinkName
  compUnsinkName
  (error "impossible")  -- scope is not used, but has to be provided in general
  pat
  (\(UnsinkName unsink) _ _ -> unsink)

-- | Auxiliary structure for unsinking names.
-- Used in 'unsinkNamePattern'.
--
-- @since 0.1.0
newtype UnsinkName n l (o :: S) (o' :: S) = UnsinkName (Name l -> Maybe (Name n))

-- | Trivial unsinking. If no scope extension took place, any name is free (since it cannot be bound by anything).
--
-- @since 0.1.0
idUnsinkName :: UnsinkName n n o o'
idUnsinkName = UnsinkName Just

-- | Composition of unsinking for nested binders/patterns.
--
-- @since 0.1.0
compUnsinkName
  :: UnsinkName n i o o'
  -> UnsinkName i l o' o''
  -> UnsinkName n l o o''
compUnsinkName (UnsinkName f) (UnsinkName g)
  = UnsinkName (\name -> g name >>= f)

-- * Sets of names, and scope restriction
--
-- The foil accounts for scope /extension/: 'NameBinder' adds names, 'Ext' is
-- the erasable evidence, and 'sink' is a coercion. Restriction is the other
-- direction, and it needs no new constraint class. Read from the other end,
-- @'Ext' m n@ /is/ the statement that every name of @m@ is a name of @n@, and
-- the runtime witness of it is the smaller 'Scope'.
--
-- What restriction does need is a way to talk about a /subset/ of the names in
-- scope, which is 'NameSet', and a way to cut a scope down to one, which is
-- 'withRestrictedScope'. Unlike extension, restriction cannot be a pure
-- coercion. 'sink' is sound because a term\'s support is contained in its
-- scope, and the converse has no such invariant, so it has to be tested.

-- | A set of names of scope @n@.
--
-- This is not a 'Scope': a 'Scope' is /all/ the names in scope, and the foil
-- relies on that (it is what freshness is tested against, and what 'Distinct'
-- speaks about). A 'NameSet' is any subset of them, such as the names a term
-- uses or the assumptions a declaration depends on, and carries no such
-- invariant.
--
-- '<>' is union and 'mempty' is empty, so a 'NameSet' can be accumulated with
-- 'foldMap'.
--
-- @since 0.4.0
newtype NameSet (n :: S) = UnsafeNameSet RawScope
  deriving newtype (NFData, Eq, Semigroup, Monoid)

-- | An empty set of names.
--
-- @since 0.4.0
emptyNameSet :: NameSet n
emptyNameSet = UnsafeNameSet IntSet.empty

-- | \(O(1)\). A set of one name.
--
-- @since 0.4.0
nameSetSingleton :: Name n -> NameSet n
nameSetSingleton (UnsafeName name) = UnsafeNameSet (IntSet.singleton name)

-- | \(O(\min(n,W))\). Add a name to a set.
--
-- @since 0.4.0
nameSetInsert :: Name n -> NameSet n -> NameSet n
nameSetInsert (UnsafeName name) (UnsafeNameSet names) =
  UnsafeNameSet (IntSet.insert name names)

-- | \(O(\min(n,W))\). Is this name in the set?
--
-- @since 0.4.0
nameSetMember :: Name n -> NameSet n -> Bool
nameSetMember (UnsafeName name) (UnsafeNameSet names) = IntSet.member name names

-- | Is the set empty?
--
-- @since 0.4.0
nameSetNull :: NameSet n -> Bool
nameSetNull (UnsafeNameSet names) = IntSet.null names

-- | How many names are in the set?
--
-- @since 0.4.0
nameSetSize :: NameSet n -> Int
nameSetSize (UnsafeNameSet names) = IntSet.size names

-- | The names in the set, in ascending order of their identifiers.
--
-- @since 0.4.0
nameSetToList :: NameSet n -> [Name n]
nameSetToList (UnsafeNameSet names) = Prelude.map UnsafeName (IntSet.toAscList names)

-- | A set of the given names.
--
-- @since 0.4.0
nameSetFromList :: [Name n] -> NameSet n
nameSetFromList names = UnsafeNameSet (IntSet.fromList (Prelude.map nameId names))

-- | A set of names sinks like anything else: rename each of its names.
--
-- As always, the proof is what makes 'sink' a coercion here, and a coercion is
-- what it has to be for a support computed under a binder to be usable in the
-- scope outside it without rebuilding the set.
instance Sinkable NameSet where
  sinkabilityProof rename = nameSetFromList . Prelude.map rename . nameSetToList

-- | All the names in a scope.
--
-- @since 0.4.0
scopeToNameSet :: Scope n -> NameSet n
scopeToNameSet (UnsafeScope names) = UnsafeNameSet names

-- | The names a pattern binds.
--
-- @since 0.4.0
nameSetOfPattern :: CoSinkable binder => binder n l -> NameSet l
nameSetOfPattern binder = UnsafeNameSet bound
  where
    UnsafeNameBinders bound = fromNameBindersList (nameBinderListOf binder)

-- | \(O(\min(n,W))\). Does the scope contain every name in the set?
--
-- This is the test that restriction of a term comes down to, so it is the one
-- place a restriction is paid for: compare a term\'s support against the scope
-- it is to be restricted to.
--
-- @since 0.4.0
nameSetSubsetOfScope :: NameSet l -> Scope n -> Bool
nameSetSubsetOfScope (UnsafeNameSet names) (UnsafeScope scope) =
  names `IntSet.isSubsetOf` scope

-- | Drop the names a pattern binds, taking a set of names of the inner scope to
-- a set of names of the outer one.
--
-- This is 'unsinkNamePattern' for a whole set at once, and \(O(\min(n,W))\)
-- rather than one membership test per name. Removing the pattern\'s names is
-- right even when one of them shares a raw name with the enclosing scope: inside
-- the pattern that raw name denotes the binder, so no occurrence of it there is
-- an occurrence of the outer name.
--
-- @since 0.4.0
unsinkNameSet :: CoSinkable binder => binder n l -> NameSet l -> NameSet n
unsinkNameSet binder (UnsafeNameSet names) = UnsafeNameSet (names IntSet.\\ bound)
  where
    UnsafeNameBinders bound = fromNameBindersList (nameBinderListOf binder)

-- | Cut a scope down to a subset of its names.
--
-- The names must be names of @n@; nothing checks it, which is why this is the
-- only entry point and takes a 'NameSet' rather than a bare @IntSet@. The
-- continuation gets @'Ext' m n@, so anything living in the smaller scope can be
-- 'sink'ed back into the larger one for free, and @'Distinct' m@, since a subset
-- of distinct names is distinct.
--
-- __Note on allocation.__ A name allocated from the restricted scope is fresh
-- with respect to @m@ and /not/ to @n@, so it may collide with a name of @n@
-- that the restriction dropped. This is sound, since @'Ext' m n@ gives no way
-- to move a term of @n@ into a scope extending @m@. It does mean that a
-- restricted scope is for inspecting and restricting terms, and not a base to
-- build new binders on and then mix with the original scope.
--
-- @since 0.4.0
withRestrictedScope
  :: forall n r. Distinct n
  => NameSet n
  -- ^ Names to keep. Must be names of @n@.
  -> (forall m. (Ext m n, Distinct m) => Scope m -> r)
  -> r
withRestrictedScope (UnsafeNameSet names) cont =
  unsafeAssertRestricted @n (UnsafeScope names) cont

-- | Unsafely declare that a scope is a restriction of scope @n@.
-- Used in 'withRestrictedScope'.
--
-- @since 0.4.0
unsafeAssertRestricted
  :: forall n m r. Scope m -> ((Ext m n, Distinct m) => Scope m -> r) -> r
unsafeAssertRestricted scope cont =
  case unsafeDistinct @m of
    Distinct -> case unsafeExt @m @n of
      Ext -> cont scope

-- * Unification of binders

-- | Unification result for two binders,
-- extending some common scope to scopes @l@ and @r@ respectively.
--
-- Due to the implementation of the foil, we can often rename binders efficiently,
-- by renaming binders only in one of the two unified terms.
--
-- @since 0.0.3
data UnifyNameBinders (pattern :: S -> S -> Type) n l r where
  -- | Binders are the same, proving that type parameters @l@ and @r@
  -- are in fact equivalent.
  SameNameBinders
    :: NameBinders n l  -- ^ /Unordered/ set of binders in the unified pattern (from any of the original patterns).
    -> UnifyNameBinders pattern n l l
  -- | It is possible to safely rename the left binder
  -- to match the right one.
  RenameLeftNameBinder
    :: NameBinders n r                    -- ^ /Unordered/ set of binders in the unified pattern (the binders from the right pattern).
    -> (NameBinder n l -> NameBinder n r) -- ^ Binder renaming for the left pattern.
    -> UnifyNameBinders pattern n l r
  -- | It is possible to safely rename the right binder
  -- to match the left one.
  RenameRightNameBinder
    :: NameBinders n l                    -- ^ /Unordered/ set of binders in the unified pattern (the binders from the left pattern).
    -> (NameBinder n r -> NameBinder n l) -- ^ Binder renaming for the right pattern.
    -> UnifyNameBinders pattern n l r
  -- | It is necessary to rename both binders.
  RenameBothBinders
    :: NameBinders n lr                     -- ^ /Unordered/ set of binders in the unified pattern
    -> (NameBinder n l -> NameBinder n lr)  -- ^ Binder renaming for the left pattern.
    -> (NameBinder n r -> NameBinder n lr)  -- ^ Binder renaming for the right pattern.
    -> UnifyNameBinders pattern n l r
  -- | Cannot unify to (sub)patterns.
  NotUnifiable :: UnifyNameBinders pattern n l r

-- | Unify binders either by asserting that they are the same,
-- or by providing a /safe/ renaming function to convert one binder to another.
--
-- When the binders differ, the one with the /larger/ name is renamed towards the
-- one with the smaller name. The direction is deliberate, but it is not what
-- makes the renaming safe.
--
-- The renaming returned here is not applied by substituting names blindly.
-- Callers push it through a term with
-- 'Control.Monad.Foil.Relative.liftRM', which refreshes a binder whenever it
-- would capture. So the target name may well be used by a binder /inside/ the
-- term being renamed, and the result is still correct. Binder names do not
-- always grow with depth: a term built in a small scope keeps its small binder
-- names when 'sink' places it in a larger one.
--
-- @since 0.0.3
unifyNameBinders
  :: forall i l r pattern. Distinct i
  => NameBinder i l -- ^ Left pattern.
  -> NameBinder i r -- ^ Right pattern.
  -> UnifyNameBinders pattern i l r
unifyNameBinders l@(UnsafeNameBinder (UnsafeName i1)) r@(UnsafeNameBinder (UnsafeName i2))
  | i1 == i2  = case assertDistinct l of
      Distinct -> unsafeCoerce (SameNameBinders (nameBindersSingleton l))  -- equal names extend scopes equally
  | i1 < i2   = RenameRightNameBinder (nameBindersSingleton l) $ \(UnsafeNameBinder (UnsafeName i'')) ->
      if i'' == i2 then UnsafeNameBinder (UnsafeName i1) else UnsafeNameBinder (UnsafeName i'')
  | otherwise = RenameLeftNameBinder (nameBindersSingleton r) $ \(UnsafeNameBinder (UnsafeName i')) ->
      if i'  == i1 then UnsafeNameBinder (UnsafeName i2) else UnsafeNameBinder (UnsafeName i')

-- | Unsafely merge results of unification for nested binders/patterns.
-- Used in 'andThenUnifyPatterns'.
--
-- @since 0.1.0
unsafeMergeUnifyBinders :: UnifyNameBinders pattern a a' a'' -> UnifyNameBinders pattern a''' b' b'' -> UnifyNameBinders pattern a b' b''
unsafeMergeUnifyBinders = \case

  SameNameBinders x -> \case
    SameNameBinders y -> SameNameBinders (x `unsafeMergeNameBinders` y)
    RenameLeftNameBinder y f -> RenameLeftNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce f)
    RenameRightNameBinder y g -> RenameRightNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce g)
    RenameBothBinders y f g -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g)
    NotUnifiable -> NotUnifiable

  RenameLeftNameBinder x f -> \case
    SameNameBinders y -> RenameLeftNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce f)
    RenameLeftNameBinder y g -> RenameLeftNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce f . unsafeCoerce g)
    RenameRightNameBinder y g -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g)
    RenameBothBinders y f' g -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f . unsafeCoerce f') (unsafeCoerce g)
    NotUnifiable -> NotUnifiable

  RenameRightNameBinder x g -> \case
    SameNameBinders y -> RenameRightNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce g)
    RenameLeftNameBinder y f -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g)
    RenameRightNameBinder y g' -> RenameRightNameBinder (x `unsafeMergeNameBinders` y) (unsafeCoerce g . unsafeCoerce g')
    RenameBothBinders y f g' -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g . unsafeCoerce g')
    NotUnifiable -> NotUnifiable

  RenameBothBinders x f g -> \case
    SameNameBinders y -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g)
    RenameLeftNameBinder y f' -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f . unsafeCoerce f') (unsafeCoerce g)
    RenameRightNameBinder y g' -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f) (unsafeCoerce g . unsafeCoerce g')
    RenameBothBinders y f' g' -> RenameBothBinders (x `unsafeMergeNameBinders` y) (unsafeCoerce f . unsafeCoerce f') (unsafeCoerce g . unsafeCoerce g')
    NotUnifiable -> NotUnifiable

  NotUnifiable -> const (NotUnifiable)

-- | Chain unification of nested patterns.
--
-- @since 0.1.0
andThenUnifyPatterns
  :: (UnifiablePattern pattern, Distinct l, Distinct l')
  => UnifyNameBinders pattern n l l'    -- ^ Unifying action for some outer patterns.
  -> (pattern l r, pattern l' r')       -- ^ Two nested patterns (cannot be unified directly since they extend different scopes).
  -> UnifyNameBinders pattern n r r'
andThenUnifyPatterns u (l, r) = unsafeMergeUnifyBinders u (unifyPatterns (unsafeCoerce l) r)

-- | Chain unification of nested patterns with 'NameBinder's.
--
-- @since 0.1.0
andThenUnifyNameBinders
  :: (UnifiablePattern pattern, Distinct l, Distinct l')
  => UnifyNameBinders pattern n l l'    -- ^ Unifying action for some outer patterns.
  -> (NameBinder l r, NameBinder l' r') -- ^ Two nested binders (cannot be unified directly since they extend different scopes).
  -> UnifyNameBinders pattern n r r'
andThenUnifyNameBinders u (l, r) = unsafeMergeUnifyBinders u (unifyNameBinders (unsafeCoerce l) r)

-- | An /unordered/ collection of 'NameBinder's, that together extend scope @n@ to scope @l@.
--
-- For an ordered version see 'NameBinderList'.
--
-- @since 0.1.0
newtype NameBinders (n :: S) (l :: S) = UnsafeNameBinders IntSet

-- | /Unsafely/ merge sets of binders (via set union).
--
-- @since 0.1.0
unsafeMergeNameBinders :: NameBinders a b -> NameBinders c d -> NameBinders n l
unsafeMergeNameBinders (UnsafeNameBinders x) (UnsafeNameBinders y) = UnsafeNameBinders (x <> y)

-- | An empty set of binders keeps the scope as is.
--
-- @since 0.1.0
emptyNameBinders :: NameBinders n n
emptyNameBinders = UnsafeNameBinders IntSet.empty

-- | Composition of sets of binders.
--
-- @since 0.1.0
mergeNameBinders :: NameBinders n i -> NameBinders i l -> NameBinders n l
mergeNameBinders = unsafeMergeNameBinders

-- | A singleton name binder set.
--
-- @since 0.1.0
nameBindersSingleton :: NameBinder n l -> NameBinders n l
nameBindersSingleton binder = UnsafeNameBinders (IntSet.singleton (nameId (nameOf binder)))

-- | An /ordered/ collection (list) of 'NameBinder's, that together extend scope @n@ to scope @l@.
--
-- For an unordered version see 'NameBinders'.
--
-- @since 0.1.0
data NameBinderList n l where
  -- | An empty list of binders keeps the scope as is.
  NameBinderListEmpty :: NameBinderList n n
  -- | A non-empty list of binders.
  NameBinderListCons
    :: NameBinder n i       -- ^ Outermost binder.
    -> NameBinderList i l   -- ^ Remaining list of binders.
    -> NameBinderList n l

-- | Convert an unordered set of name binders into an ordered list (with some order).
--
-- @since 0.1.0
nameBindersList :: NameBinders n l -> NameBinderList n l
nameBindersList (UnsafeNameBinders names) = go (IntSet.toList names)
  where
    go []     = unsafeCoerce NameBinderListEmpty
    go (x:xs) = NameBinderListCons (UnsafeNameBinder (UnsafeName x)) (go xs)

-- | The raw names a list of binders binds, outermost first.
--
-- @since 0.4.0
rawNameBinderList :: NameBinderList n l -> [RawName]
rawNameBinderList NameBinderListEmpty = []
rawNameBinderList (NameBinderListCons binder binders) =
  nameId (nameOf binder) : rawNameBinderList binders

-- | Keep only those binders of a list whose names are in a given set.
--
-- This is the /thinning/ of a chain of binders, and it is what turns a support
-- into a smaller chain in one step. The alternative, asking
-- 'Control.Monad.Free.Foil.unsinkAST' at
-- every binder whether the term can do without it, walks the term once per
-- binder, whereas a caller can compute the support once and thin against it.
--
-- The thinned scope @m@ is produced rather than given, because there is nothing
-- to give: a term\'s relevant scope (see @withRelevantScope@) is a subset of
-- @l@ and generally not an extension of @n@, since a term need not use
-- everything already in scope. What comes back is @n@ extended by the binders
-- that survived, with @Ext n m@ and @Ext m l@ to place it between the two.
--
-- The set is taken as given. For a chain whose binders carry types, or anything
-- else living in the intermediate scopes, the caller has to close the set under
-- whatever those mention before thinning by it, since dropping a binder that a
-- surviving binder\'s type refers to would leave that type unplaceable. The
-- library cannot do that closure, having no view of what a binder carries.
--
-- @since 0.4.0
withThinnedNameBinderList
  :: forall n l r. Distinct n
  => NameSet l            -- ^ Names to keep, closed under whatever the binders carry.
  -> NameBinderList n l   -- ^ The chain to thin.
  -> (forall m. (Ext n m, Ext m l, Distinct m) => NameBinderList n m -> r)
  -> r
withThinnedNameBinderList (UnsafeNameSet keep) binders cont =
    unsafeAssertThinned @n @l
      (go (Prelude.filter (`IntSet.member` keep) (rawNameBinderList binders))) cont
  where
    go :: forall m m'. [RawName] -> NameBinderList m m'
    go []       = unsafeCoerce NameBinderListEmpty
    go (x : xs) = NameBinderListCons (UnsafeNameBinder (UnsafeName x)) (go xs)

-- | Unsafely place a chain of binders between two scopes.
--
-- Sound for a chain thinned out of @n@ to @l@: its names are those of @n@ plus
-- some of the binders between @n@ and @l@, so it extends @n@, is extended by
-- @l@, and is distinct because @l@ was.
--
-- @since 0.4.0
unsafeAssertThinned
  :: forall n l m r
   . NameBinderList n m
  -> ((Ext n m, Ext m l, Distinct m) => NameBinderList n m -> r)
  -> r
unsafeAssertThinned binders cont =
  case unsafeDistinct @m of
    Distinct -> case unsafeExt @n @m of
      Ext -> case unsafeExt @m @l of
        Ext -> cont binders

-- | Add a binder to the end of an (ordered) list of binders.
--
-- Note that 'NameBinderListCons' adds a binder to the /front/ of the list, which
-- is the outermost position. This adds one to the innermost position instead.
--
-- @since 0.3.1
snocNameBinderList :: NameBinderList n i -> NameBinder i l -> NameBinderList n l
snocNameBinderList NameBinderListEmpty binder =
  NameBinderListCons binder NameBinderListEmpty
snocNameBinderList (NameBinderListCons binder binders) binder' =
  NameBinderListCons binder (snocNameBinderList binders binder')

-- | Concatenate two (ordered) lists of binders, the second extending the scope
-- that the first extends to.
--
-- @since 0.3.1
concatNameBinderLists :: NameBinderList n i -> NameBinderList i l -> NameBinderList n l
concatNameBinderLists NameBinderListEmpty binders = binders
concatNameBinderLists (NameBinderListCons binder binders) binders' =
  NameBinderListCons binder (concatNameBinderLists binders binders')

-- | Convert an ordered list of name binders into an unordered set.
--
-- @since 0.1.0
fromNameBindersList :: NameBinderList n l -> NameBinders n l
fromNameBindersList = UnsafeNameBinders . IntSet.fromList . go
  where
    go :: NameBinderList n l -> [RawName]
    go NameBinderListEmpty                 = []
    go (NameBinderListCons binder binders) = nameId (nameOf binder) : go binders

instance CoSinkable NameBinders where
  coSinkabilityProof _rename (UnsafeNameBinders names) cont =
    cont unsafeCoerce (UnsafeNameBinders names)

  withPattern withBinder unit comp scope binders cont =
    withPattern withBinder unit comp scope (nameBindersList binders) $ \f binders' scope' ->
      cont f (fromNameBindersList binders') scope'

instance CoSinkable NameBinderList where
  coSinkabilityProof rename NameBinderListEmpty cont = cont rename NameBinderListEmpty
  coSinkabilityProof rename (NameBinderListCons binder binders) cont =
    coSinkabilityProof rename binder $ \rename' binder' ->
      coSinkabilityProof rename' binders $ \rename'' binders' ->
        cont rename'' (NameBinderListCons binder' binders')

  withPattern withBinder unit comp scope binders cont = case binders of
    NameBinderListEmpty -> cont unit NameBinderListEmpty scope
    NameBinderListCons x xs ->
      withBinder scope x $ \f x' ->
        let scope' = extendScope x' scope
        in withPattern withBinder unit comp scope' xs $ \f' xs' scope'' ->
            cont (comp f f') (NameBinderListCons x' xs') scope''

-- ** Pattern combinators

-- | An empty pattern type specifies zero possibilities for patterns.
--
-- This type can be used to specify that patterns are not possible.
--
-- @since 0.1.0
data V2 (n :: S) (l :: S)

-- | Since 'V2' values logically don't exist, this witnesses the logical reasoning tool of "ex falso quodlibet".
--
-- @since 0.1.0
absurd2 :: V2 n l -> a
absurd2 v2 = case v2 of {}

instance CoSinkable V2 where
  coSinkabilityProof _ v2 _ = absurd2 v2
  withPattern _ _ _ _ v2 _ = absurd2 v2
instance UnifiablePattern V2 where
  unifyPatterns = absurd2

-- | A unit pattern type corresponds to a wildcard pattern.
--
-- @since 0.1.0
data U2 (n :: S) (l :: S) where
  U2 :: U2 n n  -- ^ Wildcard patten does not modify the scope.

instance CoSinkable U2 where
  coSinkabilityProof rename U2 cont = cont rename U2
  withPattern _withBinder unit _combine scope U2 cont = cont unit U2 scope
instance UnifiablePattern U2 where
  unifyPatterns U2 U2 = SameNameBinders emptyNameBinders

-- ** Unifiable patterns

-- | A pattern type is unifiable if it is possible to match two
-- patterns and decide how to rename binders.
--
-- Note that the default implementation compares patterns only up to their
-- binders. See 'unifyPatterns' for what that does and does not distinguish.
--
-- @since 0.0.1
class CoSinkable pattern => UnifiablePattern pattern where
  -- | Unify two patterns and decide which binders need to be renamed.
  --
  -- @since 0.1.0
  unifyPatterns :: Distinct n => pattern n l -> pattern n r -> UnifyNameBinders pattern n l r

  -- | The default implementation flattens both patterns to their binders (via
  -- 'nameBinderListOf') and unifies the resulting 'NameBinderList's. It therefore
  -- compares only the /number and order/ of binders, and ignores
  --
  -- * the constructor, so two patterns built from /different/ constructors with
  --   the same number of binders unify;
  -- * non-binding fields (locations, sorts, literals), whatever their values;
  -- * the nesting of sub-patterns, so @(x, (y, z))@ unifies with @((x, y), z)@.
  --
  -- For most languages this is the intended notion of α-equivalence: what the
  -- body of a binding construct can refer to is precisely the pattern's binders,
  -- in order. Since α-equivalence is defined in terms of 'unifyPatterns', this
  -- also means that terms differing only in such a pattern are α-equivalent.
  --
  -- A pattern that carries semantically relevant data needs the instance
  -- written by hand instead. Use 'UnifiableInPattern' to compare non-binding
  -- fields, which also lets an instance ignore some of them deliberately, as a
  -- generated instance does for BNFC source positions.
  --
  -- A field that is /scope-indexed/, such as a telescope step's type, cannot be
  -- compared here at all, since comparing it up to α needs the ambient scope
  -- and this method is given only 'Distinct'. Write 'unifyPatternsIn' for that,
  -- and leave this one as the binder-only approximation.
  default unifyPatterns
    :: (CoSinkable pattern, Distinct n)
    => pattern n l -> pattern n r -> UnifyNameBinders pattern n l r
  unifyPatterns l r = coerce (unifyPatterns (nameBinderListOf l) (nameBinderListOf r))

  -- | Unify two patterns with the ambient scope at hand.
  --
  -- Everything in the library that compares patterns and holds a scope goes
  -- through this method, α-equivalence included, so this is the one to
  -- implement when the comparison needs a scope. Comparing the payloads of a
  -- pattern that carries them does: 'alphaEquivIn' asks for a 'Scope'.
  --
  -- Note that the verdict speaks about binders, so an instance comparing
  -- payloads has to apply the renaming the verdict prescribes before it
  -- compares them, exactly as 'Control.Monad.Free.Foil.alphaEquivScoped'
  -- applies it to the body of a scoped term. Two telescopes @(A : 𝕌) (x : A)@
  -- and @(B : 𝕌) (y : B)@ are α-equivalent, and their second payloads are only
  -- equal once the first binders have been identified.
  --
  -- The default ignores the scope and answers with 'unifyPatterns'. An instance
  -- that overrides this one should leave 'unifyPatterns' in place as the
  -- binder-only approximation rather than remove it. That is what
  -- 'unsafeEqPattern' and any caller without a scope will get, and it may be
  -- more permissive than this one, never less.
  unifyPatternsIn
    :: Distinct n
    => Scope n -> pattern n l -> pattern n r -> UnifyNameBinders pattern n l r
  unifyPatternsIn _scope = unifyPatterns

instance UnifiablePattern NameBinderList where
  unifyPatterns NameBinderListEmpty NameBinderListEmpty = SameNameBinders emptyNameBinders
  unifyPatterns (NameBinderListCons x xs) (NameBinderListCons y ys) =
    case (assertDistinct x, assertDistinct y) of
      (Distinct, Distinct) -> unifyNameBinders x y `andThenUnifyPatterns` (xs, ys)
  -- Lists of different lengths are not unifiable. This case is reachable
  -- whenever a language has patterns that bind different numbers of names --
  -- a wildcard and a variable, say -- since the default 'unifyPatterns'
  -- flattens every pattern to a 'NameBinderList'. Note that this module sets
  -- @-Wno-incomplete-patterns@, so its absence was not reported.
  unifyPatterns _ _ = NotUnifiable

-- | Comparison of scope-indexed values up to α, in a known scope.
--
-- 'unifyPatterns' is given only 'Distinct', which is enough to line up binders
-- and not enough to compare anything living in a scope. A pattern that carries
-- a payload needs this to compare its payloads against another's, which is what
-- 'unifyPatternsIn' is for.
--
-- @since 0.4.0
class AlphaEquiv (e :: S -> Type) where
  -- | Are two values of one scope α-equivalent?
  --
  -- @since 0.4.0
  alphaEquivIn :: Distinct n => Scope n -> e n -> e n -> Bool

-- | A name is α-equivalent only to itself.
instance AlphaEquiv Name where
  alphaEquivIn _scope = (==)

-- | Unification of values in patterns.
-- By default, 'Eq' instance is used, but it may be useful to ignore
-- some data in pattens (such as location annotations).
--
-- @since 0.1.0
class UnifiableInPattern a where
  -- | Unify non-binding components of a pattern.
  --
  -- @since 0.1.0
  unifyInPattern :: a -> a -> Bool
  default unifyInPattern :: Eq a => a -> a -> Bool
  unifyInPattern = (==)

instance UnifiablePattern NameBinder where
  unifyPatterns = unifyNameBinders

-- | The easiest way to compare two patterns is to check if they are the same.
-- This function is labelled /unsafe/, since we generally are interested in proper α-equivalence
-- instead of direct equality.
--
-- @since 0.1.0
unsafeEqPattern :: (UnifiablePattern pattern, Distinct n) => pattern n l -> pattern n' l' -> Bool
unsafeEqPattern l r =
  case unifyPatterns l (unsafeCoerce r) of
    SameNameBinders{} -> True
    _                 -> False

-- * Safe sinking

-- | Sinking an expression from scope @n@ into a (usualy extended) scope @l@,
-- given the renaming (injection from scope @n@ to scope @l@).
--
-- @since 0.0.1
class Sinkable (e :: S -> Type) where
  -- | An implementation of this method that typechecks
  -- proves to the compiler that the expression is indeed
  -- 'Sinkable'. However, instead of this implementation, 'sink'
  -- should be used at all call sites for efficiency.
  sinkabilityProof
    :: (Name n -> Name l)   -- ^ Map names from scope @n@ to a (possibly larger) scope @l@.
    -> e n                  -- ^ Expression with free variables in scope @n@.
    -> e l

  default sinkabilityProof
    :: (GenericK e, GSinkableK (RepK e)) => (Name n -> Name l) -> e n -> e l
  sinkabilityProof rename = toK . gsinkabilityProof1 rename . fromK

-- | Sinking a 'Name' is as simple as applying the renaming.
instance Sinkable Name where
  sinkabilityProof rename = rename

-- | A container of sinkable expressions is sinkable, elementwise.
--
-- The point of this instance is 'sinkContainer': since the proof typechecks,
-- sinking the whole container is a coercion, and does not walk its spine.
instance (Functor f, Sinkable e) => Sinkable (Compose f e) where
  sinkabilityProof rename (Compose xs) = Compose (fmap (sinkabilityProof rename) xs)

-- | Efficient version of 'sinkabilityProof'.
-- In fact, once 'sinkabilityProof' typechecks,
-- it is safe to 'sink' by coercion.
-- See Section 3.5 in [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224) for the details.
--
-- 'sink' is the base of a family of \(O(1)\) coercions, named after
-- "Data.Functor.Classes": 'sink1' sinks through one 'Functor' layer and
-- 'sink2' through a 'Bifunctor', each justified by a lifted sinkability
-- proof of its own.
--
-- Tuples and records need no private @unsafeCoerce@ helpers either. A pair
-- of sinkables is a 'sink2' ('Data.Bifunctor.Tannen.Tannen' for a whole
-- container of them), and a pair whose first component is scope-free is a
-- 'sink1' through @'Compose' f ((,) a)@. A record of sinkable fields derives
-- 'Sinkable' through 'Generics.Kind.TH.deriveGenericK' and empty 'SinkableK'
-- and 'Sinkable' instances, after which the whole record sinks in one
-- coercion. A record holding the 'Scope' itself is rightly refused, since
-- there is no @SinkableK Scope@: the scope must grow when a binder is
-- entered, so keep it beside the sinkable part and not inside it.
--
-- __Do not map 'sink' over a container.__ @'fmap' 'sink'@ walks the whole
-- spine to apply a per-element coercion, where 'sink1' is one coercion.
-- Rewrite rules turn the elementwise forms into the corresponding family
-- member where they fire, but they are best-effort (they need optimisation
-- on, and 'fmap' at a known functor is often resolved to the instance
-- method first), so write the family member directly.
--
-- @since 0.0.1
sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce
{-# INLINE [0] sink #-}

-- The phase gates on 'sink' and 'sink2' keep them from inlining before
-- these can match. The map rules activate at phase 1, once list fusion has
-- backed out and rewritten unfused pipelines back to 'map' (the same trick
-- as base's @map/coerce@). The sink2 rules finish what "bimap/sink" starts:
-- @map (bimap sink sink)@ first becomes @map sink2@, and a functor around a
-- 'Bifunctor' is a 'Bifunctor' again ('Tannen'), so that map is one
-- coercion too.
--
-- These rules mirror the hlint hints in @.hlint.yaml@; keep the two lists
-- in step. The one deliberate difference: @sink '<$>'@ has a hint but no
-- rule, since the operator inlines to 'fmap' before rules run and
-- "fmap/sink" covers it, while hlint matches surface syntax.
{-# RULES
"map/sink" [1]    Prelude.map sink      = sink1
"fmap/sink"       fmap sink             = sink1
"IntMap.map/sink" Data.IntMap.map sink  = sink1
"Map.map/sink"    Data.Map.map sink     = sink1
"bimap/sink"      bimap sink sink       = sink2
"map/sink2" [1]   Prelude.map sink2     = \xs -> runTannen (sink2 (Tannen xs))
"fmap/sink2"      fmap sink2            = \xs -> runTannen (sink2 (Tannen xs))
  #-}

-- | Sink an entire container of sinkable expressions, in \(O(1)\): 'sink'
-- lifted through one 'Functor' layer, justified by the 'Sinkable' instance
-- of 'Compose'.
--
-- The soundness argument for 'sink' extends to a container of sinkables, such
-- as an 'Data.IntMap.IntMap' of terms, a 'Data.Map.Map' keyed by something
-- else, or a list of them. So there is no need to walk the spine with
-- @'fmap' 'sink'@, and entering a binder need not be \(O(size)\).
--
-- >>> :{
-- sinkEnv :: DExt n l => Map.Map String (Name n) -> Map.Map String (Name l)
-- sinkEnv = sink1
-- :}
--
-- A nested container is one 'Compose' away: @f (g (e n))@ is
-- @'Compose' f g (e n)@, and the composition is again a 'Functor', so
-- 'sink1' covers it too.
--
-- Two things this does /not/ cover:
--
-- * A 'Scope' is __not__ sinkable, and must not be sunk: it is the set of names
--   /in/ scope @n@, and it has to grow when a binder is entered (see 'extendScope').
-- * A 'NameMap' must stay __total__ on the names in scope ('lookupName' errors
--   otherwise), so sinking one has to be paired with adding the new binder's
--   entry (see 'addNameBinder').
--
-- @since 0.4.0
sink1 :: (Functor f, Sinkable e, DExt n l) => f (e n) -> f (e l)
sink1 = getCompose . sink . Compose

-- | The name 'sink1' had before the family existed.
--
-- @since 0.3.2
sinkContainer :: (Functor f, Sinkable e, DExt n l) => f (e n) -> f (e l)
sinkContainer = sink1
{-# DEPRECATED sinkContainer "Use sink1, its name in the sink family" #-}

-- | The sinkability proof lifted through a 'Bifunctor', with one renaming
-- per slot. Once this typechecks, sinking both slots at once is a coercion;
-- 'sink2' is to this proof exactly what 'sink' is to 'sinkabilityProof'.
--
-- @since 0.4.0
sinkabilityProof2
  :: (Bifunctor p, Sinkable e1, Sinkable e2)
  => (Name n -> Name n')    -- ^ Map names of scope @n@ into scope @n'@.
  -> (Name m -> Name m')    -- ^ Map names of scope @m@ into scope @m'@.
  -> p (e1 n) (e2 m)
  -> p (e1 n') (e2 m')
sinkabilityProof2 rename1 rename2 =
  bimap (sinkabilityProof rename1) (sinkabilityProof rename2)

-- | Sink both slots of a 'Bifunctor' of sinkables, in \(O(1)\), the two
-- scopes moving independently: the shape of 'Data.Functor.Classes.liftEq2',
-- with a coercion in place of each of the two functions.
--
-- >>> :{
-- sinkBoth :: (DExt n n', DExt m m') => (Name n, Name m) -> (Name n', Name m')
-- sinkBoth = sink2
-- :}
--
-- A container of such pairs is a 'Bifunctor' again, via
-- 'Data.Bifunctor.Tannen.Tannen', so a list of pairs of names, the shape an
-- α-equivalence test threads, also sinks in one coercion:
--
-- >>> :{
-- sinkPairs :: (DExt n n', DExt m m') => [(Name n, Name m)] -> [(Name n', Name m')]
-- sinkPairs = runTannen . sink2 . Tannen
-- :}
--
-- @since 0.4.0
sink2
  :: (Bifunctor p, Sinkable e1, Sinkable e2, DExt n n', DExt m m')
  => p (e1 n) (e2 m) -> p (e1 n') (e2 m')
sink2 = unsafeCoerce
{-# INLINE [0] sink2 #-}

-- | Extend renaming when going under a 'CoSinkable' pattern (generalized binder).
-- Note that the scope under pattern is independent of the codomain of the renaming.
--
-- This function is used to go under binders when implementing 'sinkabilityProof'
-- and is both a generalization of 'extendRenamingNameBinder' and an efficient implementation of 'coSinkabilityProof'.
--
-- @since 0.0.1
extendRenaming
  :: CoSinkable pattern
  => (Name n -> Name n')  -- ^ Map names from scope @n@ to a (possibly larger) scope @n'@.
  -> pattern n l          -- ^ A pattern that extends scope @n@ to another scope @l@.
  -> (forall l'. (Name l -> Name l') -> pattern n' l' -> r )
  -- ^ A continuation, accepting an extended renaming from @l@ to @l'@ (which itself extends @n'@)
  -- and a (possibly refreshed) pattern that extends @n'@ to @l'@.
  -> r
extendRenaming _ pattern cont =
  cont unsafeCoerce (unsafeCoerce pattern)

-- | Extend renaming of binders when going under a 'CoSinkable' pattern (generalized binder).
-- Note that the scope under pattern is independent of the codomain of the renaming.
--
-- @since 0.0.3
extendNameBinderRenaming
  :: CoSinkable pattern
  => (NameBinder i n -> NameBinder i n')  -- ^ Map names from scope @n@ to a (possibly larger) scope @n'@.
  -> pattern n l          -- ^ A pattern that extends scope @n@ to another scope @l@.
  -> (forall l'. (NameBinder n' l -> NameBinder n' l') -> pattern n' l' -> r )
  -- ^ A continuation, accepting an extended renaming from @l@ to @l'@ (which itself extends @n'@)
  -- and a (possibly refreshed) pattern that extends @n'@ to @l'@.
  -> r
extendNameBinderRenaming _ pattern cont =
  cont unsafeCoerce (unsafeCoerce pattern)

-- | Safely compose renamings of name binders.
-- The underlying implementation is
--
-- @since 0.0.3
composeNameBinderRenamings
  :: (NameBinder n i -> NameBinder n i')    -- ^ Rename binders extending scope @n@ from @i@ to @i'@.
  -> (NameBinder i' l -> NameBinder i' l')  -- ^ Rename binders extending scope @i'@ from @l@ to @l'@.
  -> (NameBinder n l -> NameBinder n l')
composeNameBinderRenamings = unsafeCoerce (flip (.))

-- | Convert renaming of name binders into renaming of names in the inner scopes.
--
-- @since 0.0.3
fromNameBinderRenaming :: (NameBinder n l -> NameBinder n l') -> Name l -> Name l'
fromNameBinderRenaming = coerce

-- | Extend renaming when going under a 'NameBinder'.
-- Note that the scope under binder is independent of the codomain of the renaming.
--
-- Semantically, this function may need to rename the binder (resulting in the new scope @l'@),
-- to make sure it does not clash with scope @n'@.
-- However, as it turns out, the foil makes it safe
-- to implement this function as a coercion.
-- See Appendix A in [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224) for the details.
--
-- This function is used to go under binders when implementing 'sinkabilityProof'.
-- A generalization of this function is 'extendRenaming' (which is an efficient version of 'coSinkabilityProof').
--
-- @since 0.0.1
extendRenamingNameBinder
  :: (Name n -> Name n')  -- ^ Map names from scope @n@ to a (possibly larger) scope @n'@.
  -> NameBinder n l       -- ^ A name binder that extends scope @n@ to another scope @l@.
  -> (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r )
  -- ^ A continuation, accepting an extended renaming from @l@ to @l'@ (which itself extends @n'@)
  -- and a (possibly refreshed) binder that extends @n'@ to @l'@.
  -> r
extendRenamingNameBinder _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

-- | 'CoSinkable' is to patterns (generalized binders)
-- what 'Sinkable' is to expressions.
--
-- See Section 2.3 of [«Free Foil: Generating Efficient and Scope-Safe Abstract Syntax»](https://arxiv.org/abs/2405.16384) for more details.
--
-- @since 0.0.1
class CoSinkable (pattern :: S -> S -> Type) where
  -- | An implementation of this method that typechecks
  -- proves to the compiler that the pattern is indeed
  -- 'CoSinkable'. However, instead of this implementation,
  -- 'extendRenaming' should be used at all call sites for efficiency.
  coSinkabilityProof
    :: (Name n -> Name n')  -- ^ Map names from scope @n@ to a (possibly larger) scope @n'@.
    -> pattern n l          -- ^ A pattern that extends scope @n@ to another scope @l@.
    -> (forall l'. (Name l -> Name l') -> pattern n' l' -> r)
    -- ^ A continuation, accepting an extended renaming from @l@ to @l'@ (which itself extends @n'@)
    -- and a (possibly refreshed) pattern that extends @n'@ to @l'@.
    -> r
  default coSinkabilityProof
    :: (GenericK pattern, GSinkableK (RepK pattern))
    => (Name n -> Name n')
    -> pattern n l
    -> (forall l'. (Name l -> Name l') -> pattern n' l' -> r)
    -> r
  coSinkabilityProof rename p cont = gsinkabilityProof2 rename (fromK @_ @pattern p) $ \rename' p' ->
    cont rename' (toK @_ @pattern p')

  -- | Generalized processing of a pattern.
  --
  -- You can see 'withPattern' as a CPS-style traversal over the binders in a pattern.
  --
  -- == Patterns that carry scoped payloads
  --
  -- Note that the ambient scope @o@ and the pattern's own scope @n@ are
  -- unrelated: 'nameBinderListOf' passes 'emptyScope' and 'namesOfPattern'
  -- passes no scope at all. The only thing relating the two is the pair of
  -- binders each step of the traversal produces, the one the pattern has and
  -- the one the callback hands back.
  --
  -- A pattern whose fields are all binders and plain data does not notice this,
  -- and can take the default implementation. A pattern carrying a field indexed
  -- by /its own scope/, such as the type of a telescope's step, does notice: to
  -- rebuild that field at @o@ it needs a renaming, and the only honest one is
  -- the identity on the raw names the pattern does not bind, corrected at the
  -- binders that were refreshed. That renaming is 'PatternTransport', and such
  -- a pattern should implement 'withPattern' by hand, threading one through the
  -- traversal. See 'transportPayload' for the whole recipe.
  --
  -- The default implementation cannot do this, since it goes through
  -- 'unsafeSetNameBinders', which replaces the binders and leaves every other
  -- field as it stands: a payload mentioning a refreshed binder would keep the
  -- name that binder used to have. Rather than answer wrongly, it refuses: a
  -- field indexed by a scope is a type error in the generic implementation,
  -- naming the field and pointing here.
  withPattern
    :: Distinct o
    => (forall x y z r'. Distinct z => Scope z -> NameBinder x y -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r') -> r')
    -- ^ Processing of a single 'NameBinder', this will be applied to each binder in a pattern.
    -> (forall x z z'. DExt z z' => f x x z z')
    -- ^ Result in case no binders are present. This can be seen as scope-indexed 'mempty'.
    -> (forall x y y' z z' z''. (DExt z z', DExt z' z'') => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -- ^ Composition of results for nested binders/patterns. This can be seen as scope-indexed 'mappend'.
    -> Scope o
    -- ^ Ambient scope.
    -> pattern n l
    -- ^ Pattern to process.
    -> (forall o'. DExt o o' => f n l o o' -> pattern o o' -> Scope o' -> r)
    -- ^ Continuation, accepting the result for the entire pattern, a (possibly refreshed) pattern, and the scope extended by that pattern.
    -> r
  default withPattern
    :: (Distinct o, GenericK pattern, GValidNameBinders pattern (RepK pattern), GHasNameBinders (RepK pattern))
    => (forall x y z r'. Distinct z => Scope z -> NameBinder x y -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r') -> r')
    -> (forall x z z'. DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (DExt z z', DExt z' z'') => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Scope o
    -> pattern n l
    -> (forall o'. DExt o o' => f n l o o' -> pattern o o' -> Scope o' -> r)
    -> r
  withPattern = gunsafeWithPatternViaHasNameBinders

-- ** Transporting a pattern's payloads

-- | The renaming that carries a pattern's payloads into the ambient scope of
-- 'withPattern'.
--
-- A pattern may carry fields indexed by its own scope, the standard example
-- being a telescope, where each step has a type in the scope the steps before
-- it extend to. Rebuilding such a pattern at the ambient scope means rebuilding
-- those fields there too, and 'withPattern' hands the instance no renaming for
-- it. This is that renaming, accumulated as the traversal goes.
--
-- It is abstract on purpose: the only ways to build one are 'verbatimTransport'
-- and 'transportUnderBinder', which together are exactly what a correct
-- 'withPattern' does.
--
-- Soundness rests on what 'withPattern' is allowed to do. It replaces binders
-- and nothing else, so a raw name the pattern does not bind means in @o@ what
-- it meant in @n@, and the identity on raw names is a renaming from the one to
-- the other. That is the same coercion 'extendRenaming' and 'unsafeAssertFresh'
-- already perform.
--
-- @since 0.4.0
data PatternTransport (n :: S) (o :: S)
  = TransportVerbatim
    -- ^ No binder was refreshed, so raw names are unchanged throughout.
  | TransportRenamed (Name n -> Name o)
    -- ^ Some binder was refreshed, so payloads have to be traversed.

-- | The transport to start a 'withPattern' traversal with, before any binder
-- has been seen.
--
-- @since 0.4.0
verbatimTransport :: PatternTransport n o
verbatimTransport = TransportVerbatim

-- | Extend a transport by one binder of the pattern.
--
-- The names of the inner scope are the binder's own, which goes to whatever the
-- refreshed binder introduces, and the names of the outer scope, which the
-- transport so far already answers for.
--
-- @since 0.4.0
transportUnderBinder
  :: PatternTransport n o
  -> NameBinder n i    -- ^ The binder as the pattern has it.
  -> NameBinder o o'   -- ^ The binder 'withPattern' handed back.
  -> PatternTransport i o'
transportUnderBinder transport binder binder'
  | TransportVerbatim <- transport, unchanged = TransportVerbatim
  | otherwise = TransportRenamed $ \name ->
      if nameId name == nameId (nameOf binder)
        then nameOf binder'
        else unsafeCoerce (transportName transport (unsafeCoerce name))
  where
    unchanged = nameId (nameOf binder) == nameId (nameOf binder')

-- | Carry a payload along a transport.
--
-- The 'Sinkable' instance does the walking, and only when it has to. While no
-- binder has been refreshed the payload is taken over as it stands, so the
-- traversals that never rename ('extendScopePattern', 'namesOfPattern',
-- 'nameBinderListOf') do not walk payloads at all.
--
-- The whole recipe for a payload-carrying pattern, at a telescope of labelled
-- steps:
--
-- > instance Sinkable e => CoSinkable (Telescope label e) where
-- >   withPattern withBinder unit comp = go verbatimTransport
-- >     where
-- >       go _transport _scope TelescopeEmpty cont = cont unit TelescopeEmpty
-- >       go transport scope (TelescopeCons label payload binder rest) cont =
-- >         withBinder scope binder $ \fbinder binder' ->
-- >           go (transportUnderBinder transport binder binder')
-- >              (extendScope binder' scope) rest $ \frest rest' ->
-- >             cont (comp fbinder frest)
-- >               (TelescopeCons label (transportPayload transport payload)
-- >                              binder' rest')
--
-- Note which transport each payload takes: the one accumulated /before/ its own
-- binder, since that is the scope the payload lives in.
--
-- @since 0.4.0
transportPayload :: Sinkable e => PatternTransport n o -> e n -> e o
transportPayload TransportVerbatim         = unsafeCoerce
transportPayload (TransportRenamed rename) = sinkabilityProof rename

-- | Carry a single name along a transport.
--
-- @since 0.4.0
transportName :: PatternTransport n o -> Name n -> Name o
transportName TransportVerbatim         = unsafeCoerce
transportName (TransportRenamed rename) = rename

-- | Auxiliary data structure for collecting name binders. Used in 'nameBinderListOf'.
--
-- @since 0.2.0
newtype WithNameBinderList r n l (o :: S) (o' :: S) = WithNameBinderList (NameBinderList l r -> NameBinderList n r)

-- | Empty list of name binders (identity).
--
-- @since 0.2.0
idWithNameBinderList :: DExt o o' => WithNameBinderList r n n o o'
idWithNameBinderList = WithNameBinderList id

-- | Concatenating lists of name binders (compose).
--
-- @since 0.2.0
compWithNameBinderList
  :: (DExt o o', DExt o' o'')
  => WithNameBinderList r n i o o'
  -> WithNameBinderList r i l o' o''
  -> WithNameBinderList r n l o o''
compWithNameBinderList (WithNameBinderList f) (WithNameBinderList g) =
  WithNameBinderList (f . g)

-- | Collect name binders of a generalized pattern into a name binder list,
-- which can be more easily traversed.
--
-- @since 0.2.0
nameBinderListOf :: (CoSinkable binder) => binder n l -> NameBinderList n l
nameBinderListOf pat = withPattern
  (\_scope' binder k ->
    unsafeAssertFresh binder $ \binder' ->
      k (WithNameBinderList (NameBinderListCons binder)) binder')
  idWithNameBinderList
  compWithNameBinderList
  emptyScope
  pat
  (\(WithNameBinderList f) _ _ -> f NameBinderListEmpty)

instance CoSinkable NameBinder where
  coSinkabilityProof _rename (UnsafeNameBinder name) cont =
    cont unsafeCoerce (UnsafeNameBinder name)

  withPattern withBinder _ _ scope binder cont =
    withBinder scope binder $ \f binder' ->
      cont f binder' (extendScope binder' scope)

-- * Safe substitions

-- | A substitution is a mapping from names in scope @i@
-- to expressions @e o@ in scope @o@.
--
-- @since 0.0.1
newtype Substitution (e :: S -> Type) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (e o))

-- | Apply substitution to a given name.
--
-- @since 0.0.1
{-# INLINABLE lookupSubst #-}
lookupSubst :: InjectName e => Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution env) (UnsafeName name) =
    case IntMap.lookup name env of
        Just ex -> ex
        Nothing -> injectName (UnsafeName name)

-- | Identity substitution maps all names to expresion-variables.
--
-- @since 0.0.1
identitySubst
  :: InjectName e => Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

-- | Whether a substitution maps every name to itself (see 'addRename',
-- which deletes identity renames, so this is one null test).
--
-- @since 0.4.0
nullSubst :: Substitution e i o -> Bool
nullSubst (UnsafeSubstitution env) = IntMap.null env

-- | An empty substitution from an empty scope.
--
-- @since 0.2.0
voidSubst :: Substitution e VoidS n
voidSubst = UnsafeSubstitution IntMap.empty

-- | Extend substitution with a particular mapping.
--
-- @since 0.0.1
{-# INLINABLE addSubst #-}
addSubst
  :: Substitution e i o
  -> NameBinder i i'
  -> e o
  -> Substitution e i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName name)) ex
  = UnsafeSubstitution (IntMap.insert name ex env)

-- | Extend a substitution with a value for each binder of a pattern, in the
-- order the pattern binds them.
--
-- @since 0.2.0
addSubstPattern
  :: CoSinkable binder
  => Substitution e i o
  -> binder i i'
  -> [e o]
  -> Substitution e i' o
addSubstPattern subst pat = addSubstList subst (nameBinderListOf pat)

-- | Extend a substitution with a value for each binder of a chain, in order.
-- Fails with 'error' when the list of values is too short.
--
-- @since 0.2.0
addSubstList
  :: Substitution e i o
  -> NameBinderList i i'
  -> [e o]
  -> Substitution e i' o
addSubstList subst NameBinderListEmpty _ = subst
addSubstList subst (NameBinderListCons binder binders) (x:xs) =
  addSubstList (addSubst subst binder x) binders xs
addSubstList _ _ [] = error "cannot add a binder to Substitution since the value list does not have enough elements"

-- | Add variable renaming to a substitution.
--
-- When the binder is mapped to its own name, the name is /deleted/ from the
-- substitution rather than mapped to itself. This is an optimization, but it is
-- not only an optimization: it is also how the binder shadows an outer binding
-- of the same raw name, so the delete cannot be skipped even when nothing is
-- being renamed. See 'withRefreshedPattern' for why that rules out an
-- all-binders-fresh fast path.
--
-- @since 0.0.1
{-# INLINABLE addRename #-}
addRename :: InjectName e => Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
    | otherwise = addSubst s b (injectName n)

-- | Substitutions are sinkable as long as corresponding expressions are.
instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution env) =
    UnsafeSubstitution (fmap (sinkabilityProof rename) env)

-- * 'Name' maps

-- | A /total/ map from names in scope @n@ to elements of type @a@.
--
-- @since 0.0.1
newtype NameMap (n :: S) a = NameMap { getNameMap :: IntMap a } deriving (Functor, Foldable, Traversable)

-- | An empty map belongs in the empty scope.
--
-- @since 0.0.1
emptyNameMap :: NameMap VoidS a
emptyNameMap = NameMap IntMap.empty

-- | Map over a 'NameMap', with the name each value belongs to.
--
-- This is the keyed version of the derived 'Functor' instance. It cannot change
-- which names the map is defined on, so a map that was total stays total, which
-- is what makes it a safe way to build a 'Substitution' out of one: see
-- 'nameMapToSubstitution'.
--
-- @since 0.4.0
mapWithName :: (Name n -> a -> b) -> NameMap n a -> NameMap n b
mapWithName f (NameMap m) = NameMap (IntMap.mapWithKey (f . UnsafeName) m)

-- | Convert a 'NameMap' of expressions into a 'Substitution'.
--
-- @since 0.2.0
nameMapToSubstitution :: NameMap i (e o) -> Substitution e i o
nameMapToSubstitution (NameMap m) = (UnsafeSubstitution m)

-- | Convert a 'NameMap' of expressions into a 'Scope'.
--
-- @since 0.3.0
nameMapToScope :: NameMap n a -> Scope n
nameMapToScope (NameMap m) = UnsafeScope (IntMap.keysSet m)

-- | Extend a map with multiple mappings (by repeatedly applying 'addNameBinder').
--
-- Note that the input list is expected to have __at least__ the same number of elements
-- as there are binders in the input pattern (generalized binder).
--
-- @since 0.2.0
addNameBinders :: CoSinkable binder => binder n l -> [a] -> NameMap n a -> NameMap l a
addNameBinders pat = addNameBinderList (nameBinderListOf pat)

-- | Extend a map with multiple mappings (by repeatedly applying 'addNameBinder').
--
-- Note that the input list is expected to have __at least__ the same number of elements
-- as there are binders in the input name binder list.
--
-- See also 'addNameBinders' for a generalized version.
--
-- @since 0.2.0
addNameBinderList :: NameBinderList n l -> [a] -> NameMap n a -> NameMap l a
addNameBinderList NameBinderListEmpty _ = id
addNameBinderList (NameBinderListCons binder binders) (x:xs) =
  addNameBinderList binders xs . addNameBinder binder x
addNameBinderList _ [] = error "cannot add a binder to NameMap since the value list does not have enough elements"

-- | Looking up a name should always succeed.
--
-- Note that since 'Name' is 'Sinkable', a name of scope @n@ can be looked up in a 'NameMap' for scope @l@ whenever @l@ extends @n@.
--
-- @since 0.0.1
lookupName :: Name n -> NameMap n a -> a
lookupName name (NameMap m) =
  case IntMap.lookup (nameId name) m of
    Nothing -> error "impossible: unknown name in a NameMap"
    Just x  -> x

-- | Extending a map with a single mapping.
--
-- Note that the scope parameter of the result differs from the initial map.
--
-- @since 0.0.1
addNameBinder :: NameBinder n l -> a -> NameMap n a -> NameMap l a
addNameBinder name x (NameMap m) = NameMap (IntMap.insert (nameId (nameOf name)) x m)

-- | Remove the mapping for a binder, shrinking the map back to the outer scope.
--
-- This is the inverse of 'addNameBinder', and is what a type checker wants when
-- it leaves a binder it has entered.
--
-- @since 0.3.1
popNameBinder :: NameBinder n l -> NameMap l a -> NameMap n a
popNameBinder binder (NameMap m) = NameMap (IntMap.delete (nameId (nameOf binder)) m)

-- | Allocate a fresh binder for each element of a list, binding each element to
-- its binder in the map.
--
-- The continuation receives the extended scope, the binders in the order of the
-- input list, and the extended map. This is the list-shaped counterpart of
-- 'withFresh', and saves a caller from threading the scope, the binders, and the
-- map through a recursion by hand.
--
-- @since 0.3.1
withFreshNameBinderList
  :: forall n a r. Distinct n
  => [a]                  -- ^ A value to bind to each fresh binder.
  -> Scope n              -- ^ The ambient scope.
  -> NameMap n a          -- ^ The map to extend.
  -> (forall l. DExt n l => Scope l -> NameBinderList n l -> NameMap l a -> r)
  -> r
withFreshNameBinderList = withFreshNameBinderListIn fullNameRange

-- | A version of 'withFreshNameBinderList' that allocates within a given
-- range (see 'withFreshIn'). This is the bulk form of range-guarded
-- allocation: pre-allocating the names of a whole unit at once and
-- allocating them one at a time are the same operation at different
-- granularity, so both extend the scope index faithfully.
--
-- Fails with 'error' when the range is exhausted.
--
-- @since 0.4.0
withFreshNameBinderListIn
  :: forall n a r. Distinct n
  => NameRange            -- ^ The reservation to allocate from.
  -> [a]                  -- ^ A value to bind to each fresh binder.
  -> Scope n              -- ^ The ambient scope.
  -> NameMap n a          -- ^ The map to extend.
  -> (forall l. DExt n l => Scope l -> NameBinderList n l -> NameMap l a -> r)
  -> r
withFreshNameBinderListIn range xs0 scope0 nameMap0 cont =
    go xs0 scope0 NameBinderListEmpty nameMap0 cont
  where
    go :: forall i r'. Distinct i
       => [a] -> Scope i -> NameBinderList n i -> NameMap i a
       -> (forall l. DExt n l => Scope l -> NameBinderList n l -> NameMap l a -> r')
       -> r'
    go [] scope binders nameMap cont' =
      case (assertDistinct binders, assertExt binders) of
        (Distinct, Ext) -> cont' scope binders nameMap
    go (x:xs) scope binders nameMap cont' =
      withFreshIn range scope $ \binder ->
        go xs
           (extendScope binder scope)
           (snocNameBinderList binders binder)
           (addNameBinder binder x nameMap)
           cont'

-- * Raw types and operations

-- | We will use 'Int' for efficient representation of identifiers.
--
-- @since 0.0.1
type Id = Int

-- | Raw name is simply an identifier.
--
-- @since 0.0.1
type RawName = Id

-- | A raw scope is a set of raw names.
--
-- @since 0.0.1
type RawScope = IntSet

-- | \(O(\min(n, W))\).
-- Generate a fresh raw name that
-- does not appear in a given raw scope.
-- The guard keeps allocation out of the negative range: names below zero
-- are reserved for interned constants, allocated by an explicit policy
-- ('withFreshIn' at a negative range) and never by this successor. Without
-- the guard, a scope holding only negative names would hand out the
-- successor of its maximum, which is a "fresh" name inside the constants'
-- region and may collide with a constant not in this scope. A scope that
-- holds 'maxBound' is reported as exhausted rather than wrapped past,
-- since the wrapped successor lands on an arbitrary small name that may
-- well be taken.
--
-- @since 0.0.1
rawFreshName :: RawScope -> RawName
rawFreshName scope
  | IntSet.null scope = 0
  | otherwise = case IntSet.findMax scope of
      m | m == maxBound -> error "rawFreshName: name space exhausted"
        | otherwise     -> max 0 (m + 1)

-- | An inclusive reservation of a contiguous range of raw names.
--
-- A range is a bound on an allocator (see 'withFreshIn'), not a set of names:
-- its runtime content is two 'Int's. A range with @lo > hi@ is empty.
--
-- @since 0.4.0
data NameRange = NameRange
  { nameRangeLo :: !RawName  -- ^ The smallest name of the reservation.
  , nameRangeHi :: !RawName  -- ^ The largest name of the reservation (inclusive).
  } deriving (Eq, Show)

-- | The range of all non-negative names.
--
-- On a scope without negative members, allocation within 'fullNameRange'
-- agrees with 'rawFreshName'. The two diverge on a scope with negative
-- members: 'rawFreshName' allocates right above the maximum, wherever that
-- lands, while 'fullNameRange' clamps allocation to non-negative names.
--
-- @since 0.4.0
fullNameRange :: NameRange
fullNameRange = NameRange 0 maxBound

-- | \(O(\min(n, W))\).
-- Generate a fresh raw name within a given range: the successor of the
-- largest scope member inside the range, or the range's low end when no
-- scope member lies inside the range. Returns 'Nothing' when the range is
-- exhausted (or empty to begin with).
--
-- The resulting name is fresh with respect to the /whole/ scope: it differs
-- from scope members inside the range by being greater, and from members
-- outside the range by being inside it.
--
-- >>> rawFreshNameIn (NameRange 10 19) (IntSet.fromList [-5, 3, 12, 100])
-- Just 13
-- >>> rawFreshNameIn (NameRange 10 19) (IntSet.fromList [42])
-- Just 10
-- >>> rawFreshNameIn (NameRange 10 19) (IntSet.fromList [3, 19])
-- Nothing
--
-- Note that the implementation must not increment either bound of the range:
-- @'IntSet.lookupLT' (hi + 1)@ would wrap around at @hi = maxBound@, and
-- @x + 1@ would wrap around at @x = hi = maxBound@. Both are guarded here,
-- and the property tests pin both cases.
--
-- @since 0.4.0
rawFreshNameIn :: NameRange -> RawScope -> Maybe RawName
rawFreshNameIn (NameRange lo hi) scope
  | lo > hi   = Nothing
  | otherwise = case IntSet.lookupLE hi scope of
      Just x | x >= lo -> if x < hi then Just (x + 1) else Nothing
      _                -> Just lo

-- | Check if a raw name is contained in a raw scope.
--
-- @since 0.0.1
rawMember :: RawName -> RawScope -> Bool
rawMember = IntSet.member

-- * Constraints

-- | Every scope is a (trivial) extension of itself.
--
-- __Important__: this class exists to assist tracking scope extensions
-- for type variables of kind 'S'.
-- Users of the foil are not supposed to implement any instances of 'ExtEndo'.
--
-- @since 0.0.1
class ExtEndo (n :: S)

-- | Some scopes are extensions of other scopes.
--
-- __Important__: this class exists to assist tracking scope extensions
-- for type variables of kind 'S'.
-- Users of the foil are not supposed to implement any instances of 'Ext'.
--
-- @since 0.0.1
class (ExtEndo n => ExtEndo l ) => Ext (n :: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

-- | Scopes with distinct names.
--
-- __Important__: this class exists to explicitly
-- mark scopes with distinct names.
-- Users of the foil are not supposed to implement any instances of 'Distinct'.
--
-- @since 0.0.1
class Distinct (n :: S)
instance Distinct VoidS

-- | Scope extensions with distinct names.
--
-- @since 0.0.1
type DExt n l = (Distinct l, Ext n l)

-- | Instances of this typeclass possess the ability to inject names.
-- Usually, this is a variable data constructor.
--
-- @since 0.0.1
class InjectName (e :: S -> Type) where
  -- | Inject names into expressions.
  --
  -- @since 0.0.1
  injectName :: Name n -> e n

-- * Kind-polymorphic sinkability

-- | One renaming per scope index of a kind-polymorphic type, which is what
-- 'sinkabilityProofK' threads through a value.
--
-- @since 0.3.0
data RenamingsK (as :: LoT k) (bs :: LoT k) where
  RNil :: RenamingsK LoT0 LoT0
  RCons :: (Name a -> Name b) -> RenamingsK as bs -> RenamingsK (a :&&: as) (b :&&: bs)
  RSkip :: RenamingsK as bs -> RenamingsK (k :&&: as) (k :&&: bs)

-- | 'Sinkable' for a type with any number of scope indices, and the class a
-- pattern derives to obtain the foil's traversals. An instance is normally
-- empty, leaving the generic implementation to walk the
-- 'Generics.Kind.RepK' of the type.
--
-- @since 0.3.0
class SinkableK (f :: S -> k) where
  -- | Rename every scope index of a value, in continuation-passing style.
  --
  -- @since 0.3.0
  sinkabilityProofK
    :: forall as bs r.
       RenamingsK as bs
    -> f :@@: as
    -> (forall cs. RenamingsK as cs -> f :@@: cs -> r)
    -> r
  default sinkabilityProofK :: forall as bs r.
      (GenericK f, GSinkableK (RepK f))
    => RenamingsK as bs
    -> f :@@: as
    -> (forall cs. RenamingsK as cs -> f :@@: cs -> r)
    -> r
  sinkabilityProofK rename e cont =
    gsinkabilityProofK rename (fromK @_ @f e) $ \rename' e' ->
      cont rename' (toK @_ @f e')

-- | Move a value between two scope index lists reached from a common one, as
-- a coercion.
--
-- @since 0.3.0
sinkK :: GSinkableK f => RenamingsK xs as -> RenamingsK xs bs -> f :@@: as -> f :@@: bs
sinkK _ _ = unsafeCoerce

instance SinkableK Name where
  sinkabilityProofK renameK@(RCons rename RNil) name cont = cont renameK (rename name)
instance SinkableK NameBinder where
  sinkabilityProofK (RCons _ RNil) (UnsafeNameBinder name) cont =
    cont (RCons unsafeCoerce RNil) (UnsafeNameBinder name)
instance SinkableK NameBinders where
  sinkabilityProofK (RCons _ RNil) (UnsafeNameBinders s) cont =
    cont (RCons unsafeCoerce RNil) (UnsafeNameBinders s)

instance GenericK NameBinderList where
  type RepK NameBinderList = ((Var0 :~~: Var1) :=>: U1) :+: Exists S
    (Field (NameBinder :$: Var1 :@: Var0) :*: Field (NameBinderList :$: Var0 :@: Var2))
  toK (L1 (SuchThat U1))                   = NameBinderListEmpty
  toK (R1 (Exists (Field x :*: Field xs))) = NameBinderListCons x xs
  fromK NameBinderListEmpty       = L1 (SuchThat U1)
  fromK (NameBinderListCons x xs) = R1 (Exists (Field x :*: Field xs))

instance GenericK V2 where
  type RepK V2 = V1
  toK _v1 = error "absurd: Generics.Kind.V1"
  fromK = absurd2

instance GenericK U2 where
  type RepK U2 = ((Var0 :~~: Var1) :=>: U1)
  toK (SuchThat U1) = U2
  fromK U2 = SuchThat U1

instance SinkableK NameBinderList
instance SinkableK V2
instance SinkableK U2

-- | 'sinkabilityProofK' at a type with exactly one scope index.
--
-- @since 0.3.0
sinkabilityProof1 :: SinkableK f => (Name n -> Name n') -> f n -> f n'
sinkabilityProof1 rename e = sinkabilityProofK (RCons rename RNil) e $ \_ e' -> unsafeCoerce e'

-- | 'gsinkabilityProofK' at a representation with one scope index.
--
-- @since 0.3.0
gsinkabilityProof1 :: GSinkableK f => (Name n -> Name n') -> f (n :&&: LoT0) -> f (n' :&&: LoT0)
gsinkabilityProof1 rename e = gsinkabilityProofK (RCons rename RNil) e $ \_ e' -> unsafeCoerce e'

-- | 'gsinkabilityProofK' at a representation with two scope indices, the
-- shape of a pattern: the outer scope is renamed by the given function, and
-- the inner one by the renaming handed to the continuation.
--
-- @since 0.3.0
gsinkabilityProof2
  :: forall f n n' l r. GSinkableK f
  => (Name n -> Name n') -> f (n :&&: l :&&: LoT0)
  -> (forall l'. (Name l -> Name l') -> f (n' :&&: l' :&&: LoT0) -> r)
  -> r
gsinkabilityProof2 rename e cont =
  gsinkabilityProofK (RCons rename (RCons id RNil)) e $ \case
    RCons (_ :: Name n -> Name n'') (RCons rename' RNil) -> \e' ->
      case unsafeCoerce (Type.Refl :: n' Type.:~: n') :: n' Type.:~: n'' of
        Type.Refl -> cont rename' e'

-- | 'gsinkabilityProofK' where the resulting index list is known, so that no
-- continuation is needed.
--
-- @since 0.3.0
gsinkabilityProofK' :: GSinkableK f => RenamingsK as bs -> f as -> f bs
gsinkabilityProofK' renameK e = gsinkabilityProofK renameK e $ \_ e' -> unsafeCoerce e'

-- | 'SinkableK' on the "Generics.Kind" representation of a type, which is
-- what the default 'sinkabilityProofK' goes through.
--
-- @since 0.3.0
class GSinkableK p where
  -- | Rename every scope index of a representation.
  --
  -- @since 0.3.0
  gsinkabilityProofK
    :: forall as bs r.
       RenamingsK as bs
    -> p as
    -> (forall cs. RenamingsK as cs -> p cs -> r)
    -> r

-- | 'sinkK' on a representation.
--
-- @since 0.3.0
gsinkK :: GSinkableK f => RenamingsK xs as -> RenamingsK xs bs -> f as -> f bs
gsinkK _ _ = unsafeCoerce

instance GSinkableK V1 where
  gsinkabilityProofK irename _v1 cont =
    cont irename (error "absurd: Generics.Kind.V1")

instance GSinkableK U1 where
  gsinkabilityProofK irename U1 cont =
    cont irename U1

instance GSinkableK f => GSinkableK (M1 i c f) where
  gsinkabilityProofK irename (M1 x) cont =
    gsinkabilityProofK irename x $ \irename' x' ->
      cont irename' (M1 x')

instance (GSinkableK f, GSinkableK g) => GSinkableK (f :+: g) where
  gsinkabilityProofK irename (L1 x) cont =
    gsinkabilityProofK irename x $ \irename' x' ->
      cont irename' (L1 x')
  gsinkabilityProofK irename (R1 x) cont =
    gsinkabilityProofK irename x $ \irename' x' ->
      cont irename' (R1 x')

instance (GSinkableK f, GSinkableK g) => GSinkableK (f :*: g) where
  gsinkabilityProofK irename (x :*: y) cont =
    gsinkabilityProofK irename x $ \irename' x' ->
      gsinkabilityProofK irename' y $ \irename'' y' ->
        cont irename'' (gsinkK irename' irename'' x' :*: y')

instance GSinkableK f => GSinkableK (Exists S f) where
  gsinkabilityProofK irename (Exists x) cont =
    gsinkabilityProofK (RCons id irename) x $ \case
      RCons _ irename' -> \x' ->
        cont irename' (Exists x')

instance {-# OVERLAPPABLE #-} GSinkableK f => GSinkableK (Exists k f) where
  gsinkabilityProofK irename (Exists x) cont =
    gsinkabilityProofK (RSkip irename) x $ \case
      RSkip irename' -> \x' ->
        cont irename' (Exists x')

instance GSinkableK f => GSinkableK ((a :~~: b) :=>: f) where
  gsinkabilityProofK irename (SuchThat x) cont =
    gsinkabilityProofK irename x $ \(irename' :: RenamingsK as cs) x' ->
      -- this is sort of safe...
      case unsafeCoerce (Type.Refl :: Interpret a cs Type.:~: Interpret a cs) :: Interpret a cs Type.:~: Interpret b cs of
        Type.Refl -> cont irename' (SuchThat x')

instance GSinkableK (Field (Kon a)) where
  gsinkabilityProofK irename (Field x) cont =
    cont irename (Field x)

instance GSinkableK (Field (Var a)) where
  gsinkabilityProofK irename (Field x) cont =
    cont irename (Field (unsafeCoerce x)) -- FIXME: unsafeCoerce?

instance (SinkableK f, ExtractRenamingK i) => GSinkableK (Field (Kon f :@: Var i)) where
  gsinkabilityProofK irename (Field x) cont =
    sinkabilityProofK (RCons (extractRenamingK @_ @i irename) RNil) x $ \case
      RCons rename' RNil -> \x' ->
        cont (putBackRenamingK @_ @i rename' irename) (Field (unsafeCoerce x')) -- unsafeCoerce?

instance SinkableK (f a) => GSinkableK (Field (Kon f :@: Kon a :@: Var0)) where
  gsinkabilityProofK irename@(RCons _ RNil) (Field x) cont =
    sinkabilityProofK irename x $ \rename' x' ->
      cont rename' (Field x')

instance SinkableK (f a b) => GSinkableK (Field (Kon f :@: Kon a :@: Kon b :@: Var0)) where
  gsinkabilityProofK irename@(RCons _ RNil) (Field x) cont =
    sinkabilityProofK irename x $ \rename' x' ->
      cont rename' (Field x')

-- | Reading one scope index out of a list of them, and putting a renaming
-- back at that position. This is what lets a generic traversal work on the
-- index a field actually mentions.
--
-- @since 0.3.0
class ExtractRenamingK (i :: TyVar k S) where
  -- | The renaming at this index.
  --
  -- @since 0.3.0
  extractRenamingK :: forall (as :: LoT k) (bs :: LoT k).
    RenamingsK as bs -> Name (Interpret (Var i) as) -> Name (Interpret (Var i) bs)
  -- | Replace the renaming at this index.
  --
  -- @since 0.3.0
  putBackRenamingK :: forall c (as :: LoT k) (bs :: LoT k).
       (Name (Interpret (Var i) as) -> Name c)
    -> RenamingsK as bs
    -> RenamingsK as (PutBackLoT i c bs)

instance ExtractRenamingK VZ where
  extractRenamingK (RCons f _fs) = f
  putBackRenamingK f (RCons _ gs) = RCons f gs

instance ExtractRenamingK x => ExtractRenamingK (VS x) where
  extractRenamingK (RCons _f fs) = extractRenamingK @_ @x fs
  putBackRenamingK f (RCons g gs) = RCons g (putBackRenamingK @_ @x f gs)

-- | 'extractRenamingK' at two indices at once, as a pattern's traversal needs.
--
-- @since 0.3.0
extractTwoRenamingsK :: forall k (i :: TyVar k S) (j :: TyVar k S) (as :: LoT k) (bs :: LoT k).
    (ExtractRenamingK i, ExtractRenamingK j)
  => RenamingsK as bs
  -> RenamingsK
      (Interpret (Var i) as :&&: Interpret (Var j) as :&&: LoT0)
      (Interpret (Var i) bs :&&: Interpret (Var j) bs :&&: LoT0)
extractTwoRenamingsK irename =
  (RCons (extractRenamingK @_ @i irename) (RCons (extractRenamingK @_ @j irename) RNil))

-- | 'putBackRenamingK' at two indices at once.
--
-- @since 0.3.0
putBackTwoRenamingsK :: forall k (i :: TyVar k S) (j :: TyVar k S) c1 c2 (as :: LoT k) (bs :: LoT k).
    (ExtractRenamingK i, ExtractRenamingK j)
  => RenamingsK
      (Interpret (Var i) as :&&: Interpret (Var j) as :&&: LoT0)
      (c1 :&&: c2 :&&: LoT0)
  -> RenamingsK as bs
  -> RenamingsK as (PutBackLoT j c2 (PutBackLoT i c1 bs))
putBackTwoRenamingsK (RCons f1 (RCons f2 RNil)) rename
  = putBackRenamingK @_ @j f2 (putBackRenamingK @_ @i f1 rename)

instance (SinkableK f, ExtractRenamingK i, ExtractRenamingK j) => GSinkableK (Field (Kon f :@: Var (i :: TyVar k S) :@: Var (j :: TyVar k S))) where
  gsinkabilityProofK irename (Field x) cont =
    sinkabilityProofK (extractTwoRenamingsK @_ @i @j irename) x $ \rename' x' ->
      case rename' of
        RCons _ (RCons _ RNil) ->
          cont (putBackTwoRenamingsK @_ @i @j rename' irename)
              (Field (unsafeCoerce x'))  -- FIXME: can we do better than unsafeCoerce?

instance (Functor f, GSinkableK (Field x)) => GSinkableK (Field (Kon f :@: x)) where
  gsinkabilityProofK irename (Field x) cont =
    cont irename (Field (fmap
      (unField . gsinkabilityProofK' @(Field x) irename . Field)
      x))

instance (Bifunctor f, GSinkableK (Field x), GSinkableK (Field y)) => GSinkableK (Field (Kon f :@: x :@: y)) where
  gsinkabilityProofK irename (Field x) cont =
    cont irename (Field (bimap
      (unField . gsinkabilityProofK' @(Field x) irename . Field)
      (unField . gsinkabilityProofK' @(Field y) irename . Field)
      x))

-- * Kind-polymorphic types with binders

-- ** Generic version of 'withPattern'

-- | Generic generalized processing of a pattern via 'GHasNameBinders'.
--
-- This can be used as a default implementation of 'withPattern'.
--
-- @since 0.3.0
gunsafeWithPatternViaHasNameBinders
  :: forall pattern f o n l r.
      (Distinct o, GenericK pattern, GValidNameBinders pattern (RepK pattern), GHasNameBinders (RepK pattern))
  => (forall x y z r'. Distinct z => Scope z -> NameBinder x y -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r') -> r')
  -- ^ Processing of a single 'NameBinder', this will be applied to each binder in a pattern.
  -> (forall x z z'. DExt z z' => f x x z z')
  -- ^ Result in case no binders are present. This can be seen as scope-indexed 'mempty'.
  -> (forall x y y' z z' z''. (DExt z z', DExt z' z'') => f x y z z' -> f y y' z' z'' -> f x y' z z'')
  -- ^ Composition of results for nested binders/patterns. This can be seen as scope-indexed 'mappend'.
  -> Scope o
  -- ^ Ambient scope.
  -> pattern n l
  -- ^ Pattern to process.
  -> (forall o'. DExt o o' => f n l o o' -> pattern o o' -> Scope o' -> r)
  -- ^ Continuation, accepting the result for the entire pattern, a (possibly refreshed) pattern, and the scope extended by that pattern.
  -> r
gunsafeWithPatternViaHasNameBinders withBinder id_ comp_ scope pat cont =
  withPattern withBinder id_ comp_ scope (ggetNameBinders pat) $ \result binders scope' ->
    cont result (gunsafeSetNameBinders (unsafeCoerce pat) binders) scope' -- FIXME: safer version

-- ** Manipulating nested 'NameBinder's
-- | If @'HasNameBinders' f@, then @f n l@ is expected to act as a binder,
-- introducing into scope @n@ some local variables, extending it to scope @l@.
-- This class allows to extract and modify the set of binders.
--
-- @since 0.3.0
class HasNameBinders f where
  -- | Extract a set of binders from a pattern.
  --
  -- @since 0.3.0
  getNameBinders :: f n l -> NameBinders n l
  getNameBinders = UnsafeNameBinders . IntSet.fromList . getNameBindersRaw

  -- | Replace binders in a pattern.
  --
  -- This function is unsafe, because it does not check if the new set of binders
  -- has the same size. It can therefore crash at runtime.
  --
  -- You should probably not use this.
  -- This is only used for 'gunsafeWithPatternViaHasNameBinders', which is then safe to use.
  --
  -- @since 0.3.0
  unsafeSetNameBinders :: f n l -> NameBinders n l' -> f n l'
  unsafeSetNameBinders e (UnsafeNameBinders m) = fst (reallyUnsafeSetNameBindersRaw e (IntSet.toList m))

  -- | Extract 'RawName's of all binders occurring in a pattern.
  --
  -- @since 0.3.0
  getNameBindersRaw :: f n l -> [RawName]
  default getNameBindersRaw :: forall n l. (GenericK f, GHasNameBinders (RepK f)) => f n l -> [RawName]
  getNameBindersRaw = ggetNameBindersRaw . fromK @_ @f @(n :&&: l :&&: LoT0)

  -- | This is a version of 'unsafeSetNameBinders'
  -- that takes in a list of 'RawName's.
  --
  -- It does not check if the given list has enough elements.
  -- It does not check if the raw names are fresh in the scope @n@.
  -- It does not check if the raw names given are distinct.
  --
  -- You should never use this. This is only used for generic implementation of 'HasNameBinders'.
  --
  -- @since 0.3.0
  reallyUnsafeSetNameBindersRaw :: f n l -> [RawName] -> (f n l', [RawName])
  default reallyUnsafeSetNameBindersRaw :: forall n l l'. (GenericK f, GValidNameBinders f (RepK f), GHasNameBinders (RepK f)) => f n l -> [RawName] -> (f n l', [RawName])
  reallyUnsafeSetNameBindersRaw e names =
    let (e', names') = greallyUnsafeSetNameBindersRaw (fromK @_ @f @(n :&&: l :&&: LoT0) e) names
     in (toK @_ @f @(n :&&: l' :&&: LoT0) e', names')

instance HasNameBinders NameBinder where
  getNameBindersRaw (UnsafeNameBinder (UnsafeName name)) = [name]
  reallyUnsafeSetNameBindersRaw _ (name:names) = (UnsafeNameBinder (UnsafeName name), names)

instance HasNameBinders NameBinderList

-- ** Generic

-- | 'getNameBinders' through the generic representation.
--
-- @since 0.3.0
ggetNameBinders :: forall f n l. (GenericK f, GHasNameBinders (RepK f)) => f n l -> NameBinders n l
ggetNameBinders = UnsafeNameBinders . IntSet.fromList . ggetNameBindersRaw . fromK @_ @f @(n :&&: l :&&: LoT0)

-- | 'unsafeSetNameBinders' through the generic representation.
--
-- @since 0.3.0
gunsafeSetNameBinders :: forall f n l l'. (GenericK f, GValidNameBinders f (RepK f), GHasNameBinders (RepK f)) => f n l -> NameBinders n l' -> f n l'
gunsafeSetNameBinders e (UnsafeNameBinders m) = toK @_ @f @(n :&&: l' :&&: LoT0) $
  fst (greallyUnsafeSetNameBindersRaw (fromK @_ @f @(n :&&: l :&&: LoT0) e) (IntSet.toList m))

-- | 'HasNameBinders' on the "Generics.Kind" representation of a pattern.
--
-- @since 0.3.0
class GHasNameBinders f where
  -- | The raw names the representation binds, in order.
  --
  -- @since 0.3.0
  ggetNameBindersRaw :: f as -> [RawName]

  -- | Replace those names, returning what is left of the list.
  --
  -- @since 0.3.0
  greallyUnsafeSetNameBindersRaw :: f as -> [RawName] -> (f bs, [RawName])

instance GHasNameBinders V1 where
  ggetNameBindersRaw _ = error "absurd: Generics.Kind.V1"
  greallyUnsafeSetNameBindersRaw _ _ = error "absurd: Generics.Kind.V1"
instance GHasNameBinders U1 where
  ggetNameBindersRaw U1 = []
  greallyUnsafeSetNameBindersRaw U1 names = (U1, names)

instance (GHasNameBinders f, GHasNameBinders g) => GHasNameBinders (f :+: g) where
  ggetNameBindersRaw (L1 x) = ggetNameBindersRaw x
  ggetNameBindersRaw (R1 x) = ggetNameBindersRaw x

  greallyUnsafeSetNameBindersRaw (L1 x) names = first L1 (greallyUnsafeSetNameBindersRaw x names)
  greallyUnsafeSetNameBindersRaw (R1 x) names = first R1 (greallyUnsafeSetNameBindersRaw x names)

-- | __A caveat.__ This instance treats the two factors as /nested/ binders,
-- and does not reject /parallel/ ones:
--
-- > data BadPattern n l = BadPattern (NameBinder n l) (NameBinder n l)
--
-- The intended shape is a chain, in which each binder extends the scope the
-- next one starts from:
--
-- > data GoodPattern n l = forall i. GoodPattern (NameBinder n i) (NameBinder i l)
--
-- Template Haskell never generates parallel binders, and writing one by hand
-- takes deliberate effort, so this is unlikely to be reached by accident.
-- Detecting and rejecting such a pattern would still be better.
instance (GHasNameBinders f, GHasNameBinders g) => GHasNameBinders (f :*: g) where
  ggetNameBindersRaw (x :*: y) = ggetNameBindersRaw x <> ggetNameBindersRaw y
  greallyUnsafeSetNameBindersRaw (x :*: y) names =
    let (x', names') = greallyUnsafeSetNameBindersRaw x names
        (y', names'') = greallyUnsafeSetNameBindersRaw y names'
     in (x' :*: y', names'')

instance GHasNameBinders f => GHasNameBinders (M1 i c f) where
  ggetNameBindersRaw (M1 x) = ggetNameBindersRaw x
  greallyUnsafeSetNameBindersRaw (M1 x) names =
    let (x', names') = greallyUnsafeSetNameBindersRaw x names
     in (M1 x', names')

instance GHasNameBinders f => GHasNameBinders (Var i :~~: Var j :=>: f) where
  ggetNameBindersRaw (SuchThat x) = ggetNameBindersRaw x

  greallyUnsafeSetNameBindersRaw :: forall as bs. (Var i :~~: Var j :=>: f) as -> [RawName] -> ((Var i :~~: Var j :=>: f) bs, [RawName])
  greallyUnsafeSetNameBindersRaw (SuchThat x) names =
    -- this is sort of safe...
    case unsafeCoerce (Type.Refl :: Interpret (Var i) bs Type.:~: Interpret (Var i) bs) :: Interpret (Var i) bs Type.:~: Interpret (Var j) bs of
      Type.Refl ->
        let (x', names') = greallyUnsafeSetNameBindersRaw x names
         in (SuchThat x', names')

instance GHasNameBinders f => GHasNameBinders (Exists k f) where
  ggetNameBindersRaw (Exists x) = ggetNameBindersRaw x
  greallyUnsafeSetNameBindersRaw (Exists x) names =
    let (x', names') = greallyUnsafeSetNameBindersRaw x names
     in (Exists x', names')

instance GHasNameBinders (Field (Kon a)) where
  ggetNameBindersRaw (Field _x) = []
  greallyUnsafeSetNameBindersRaw (Field x) names = (Field x, names)

instance GHasNameBinders (Field (Var x)) where
  ggetNameBindersRaw (Field _x) = []
  greallyUnsafeSetNameBindersRaw (Field x) names = (Field (unsafeCoerce x), names)  -- FIXME: unsafeCoerce?

instance GHasNameBinders (Field (Kon f :@: Var i)) where
  ggetNameBindersRaw (Field _x) = []
  greallyUnsafeSetNameBindersRaw (Field x) names = (Field (unsafeCoerce x), names) -- FIXME: unsafeCoerce?

instance HasNameBinders f => GHasNameBinders (Field (Kon f :@: Var i :@: Var j)) where
  ggetNameBindersRaw (Field x) = getNameBindersRaw x
  greallyUnsafeSetNameBindersRaw (Field x) names =
    let (x', names') = reallyUnsafeSetNameBindersRaw x names
     in (Field (unsafeCoerce x'), names') -- FIXME: safer version?
