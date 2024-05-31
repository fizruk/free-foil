{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
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
-- is either 'IntMap' or 'IntSet', many of the operations
-- have a worst-case complexity of \(O(\min(n,W))\).
-- This means that the operation can become linear in the size of the scope \(n\) with a maximum of \(W\)
-- — the number of bits in an 'Int' (32 or 64).
module Control.Monad.Foil.Internal where

import           Control.DeepSeq (NFData (..))
import           Data.IntMap
import qualified Data.IntMap     as IntMap
import           Data.IntSet
import qualified Data.IntSet     as IntSet
import           Data.Kind       (Type)
import           Unsafe.Coerce

-- * Safe types and operations

-- | 'S' is a data kind of scope indices.
data S
  = VoidS -- ^ 'VoidS' is the only explicit scope available to the users, representing an empty scope.
          -- All other scopes are represented with type variables,
          -- bound in rank-2 polymophic functions like 'withFreshBinder'.

-- | A safe scope, indexed by a type-level scope index 'n'.
newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData

-- | A name in a safe scope, indexed by a type-level scope index 'n'.
newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord)

-- | A name binder is a name that extends scope @n@ to a (larger) scope @l@.
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord)

-- | An empty scope (without any names).
emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

-- | \(O(\min(n,W))\).
-- Extend a scope with one name (safely).
-- Note that as long as the foil is used as intended,
-- the name binder is guaranteed to introduce a name
-- that does not appear in the initial scope.
extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName name)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert name scope)

-- | A runtime check for potential name capture.
member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

-- | Extract name from a name binder.
nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

-- | Allocate a fresh binder for a given scope.
withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r) -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

-- | Evidence that scope @n@ contains distinct names.
data DistinctEvidence (n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

-- | Unsafely declare that scope @n@ is distinct.
-- Used in 'unsafeAssertFresh'.
unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

-- | Evidence that scope @l@ extends scope @n@.
data ExtEvidence (n :: S) (l :: S) where
  Ext :: Ext n l => ExtEvidence n l

-- | Unsafely declare that scope @l@ extends scope @n@.
-- Used in 'unsafeAssertFresh'.
unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

-- | Safely produce a fresh name binder with respect to a given scope.
withFresh
  :: Distinct n => Scope n
  -> (forall l. DExt n l => NameBinder n l -> r) -> r
withFresh scope cont = withFreshBinder scope (`unsafeAssertFresh` cont)

-- | Unsafely declare that a given name (binder)
-- is already fresh in any scope @n'@.
unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

-- | A distinct scope extended with a 'NameBinder' is also distinct.
assertDistinct :: Distinct n => NameBinder n l -> DistinctEvidence l
assertDistinct _ = unsafeDistinct

-- | Safely rename (if necessary) a given name to extend a given scope.
-- This is similar to 'withFresh', except if the name does not clash with
-- the scope, it can be used immediately, without renaming.
withRefreshed
  :: Distinct o
  => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName rawName) cont
  | IntSet.member rawName rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont


-- * Safe sinking

-- | Sinking an expression from scope @n@ into a (usualy extended) scope @l@,
-- given the renaming (injection from scope @n@ to scope @l@).
class Sinkable (e :: S -> Type) where
  -- | An implementation of this method that typechecks
  -- proves to the compiler that the expression is indeed
  -- 'Sinkable'. However, instead of this implementation, 'sink'
  -- should be used at all call sites for efficiency.
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

-- | Sinking a 'Name' is as simple as applying the renaming.
instance Sinkable Name where
  sinkabilityProof rename = rename

-- | Efficient version of 'sinkabilityProof'.
-- In fact, once 'sinkabilityProof' typechecks,
-- it is safe to 'sink' by coercion.
-- See Section 3.5 in [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224) for the details.
sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

-- | Extend renaming when going under a binder.
-- Note that the scope under binder is independent of the codomain of the renaming.
--
-- Semantically, this function may need to rename the binder (resulting in the new scope @l'@),
-- to make sure it does not clash with scope @n'@.
-- However, as it turns out, the foil makes it safe
-- to implement this function as a coercion.
-- See Appendix A in [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224) for the details.
--
-- This function is used to go under binders when implementing 'sinkabilityProof'.
-- A generalization of this function is 'coSinkabilityProof'.
extendRenaming
  :: (Name n -> Name n')
  -> NameBinder n l
  -> (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r ) -> r
extendRenaming _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

-- * Safe substitions

-- | A substitution is a mapping from names in scope @i@
-- to expressions @e o@ in scope @o@.
data Substitution (e :: S -> Type) (i :: S) (o :: S) =
  UnsafeSubstitution (forall n. Name n -> e n) (IntMap (e o))

-- | Apply substitution to a given name.
lookupSubst :: Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution f env) (UnsafeName name) =
    case IntMap.lookup name env of
        Just ex -> ex
        Nothing -> f (UnsafeName name)

-- | Identity substitution maps all names to expresion-variables.
identitySubst
  :: (forall n. Name n -> e n)  -- ^ How to wrap a name into a variable.
  -> Substitution e i i
identitySubst f = UnsafeSubstitution f IntMap.empty

-- | Extend substitution with a particular mapping.
addSubst
  :: Substitution e i o
  -> NameBinder i i'
  -> e o
  -> Substitution e i' o
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName name)) ex
  = UnsafeSubstitution f (IntMap.insert name ex env)

-- | Add variable renaming to a substitution.
-- This includes the performance optimization of eliding names mapped to themselves.
addRename :: Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution f env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f (IntMap.delete name1 env)
    | otherwise = addSubst s b (f n)

-- | Substitutions are sinkable as long as corresponding expressions are.
instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)

-- * Raw types and operations

-- | We will use 'Int' for efficient representation of identifiers.
type Id = Int

-- | Raw name is simply an identifier.
type RawName = Id

-- | A raw scope is a set of raw names.
type RawScope = IntSet

-- | \(O(\min(n, W))\).
-- Generate a fresh raw name that
-- does not appear in a given raw scope.
rawFreshName :: RawScope -> RawName
rawFreshName scope | IntSet.null scope = 0
                   | otherwise = IntSet.findMax scope + 1

rawMember :: RawName -> RawScope -> Bool
rawMember = IntSet.member

-- * Constraints

-- | Every scope is a (trivial) extension of itself.
--
-- __Important__: this class exists to assist tracking scope extensions
-- for type variables of kind 'S'.
-- Users of the foil are not supposed to implement any instances of 'ExtEndo'.
class ExtEndo (n :: S)

-- | Some scopes are extensions of other scopes.
--
-- __Important__: this class exists to assist tracking scope extensions
-- for type variables of kind 'S'.
-- Users of the foil are not supposed to implement any instances of 'Ext'.
class (ExtEndo n => ExtEndo l ) => Ext (n :: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

-- | Scopes with distinct names.
--
-- __Important__: this class exists to explicitly
-- mark scopes with distinct names.
-- Users of the foil are not supposed to implement any instances of 'Distinct'.
class Distinct (n :: S)
instance Distinct VoidS

-- | Scope extensions with distinct names.
type DExt n l = (Distinct l, Ext n l)
