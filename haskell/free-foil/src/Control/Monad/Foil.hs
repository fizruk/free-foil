-- | Main definitions of the foil that can be
-- reused for specific implementations.
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
module Control.Monad.Foil (
  -- * Safe scopes, names, and binders
  S(..),
  Scope,
  Name,
  NameBinder,
  emptyScope,
  extendScope,
  extendScopePattern,
  member,
  nameOf,
  namesOfPattern,
  nameId,
  withFreshBinder,
  withFresh,
  withFreshPattern,
  withRefreshed,
  withRefreshedPattern,
  withRefreshedPattern',
  unsinkName,
  unsinkNamePattern,
  -- * Safe (co)sinking and renaming
  SinkableK(..),
  Sinkable(..),
  CoSinkable(..),
  UnsafeHasNameBinders(..),
  sink,
  extendRenaming,
  extendNameBinderRenaming,
  composeNameBinderRenamings,
  fromNameBinderRenaming,
  extendRenamingNameBinder,
  -- * Safe substitutions
  Substitution,
  lookupSubst,
  identitySubst,
  voidSubst,
  addSubst,
  addSubstPattern,
  addSubstList,
  addRename,
  -- * Unification of binders
  UnifyNameBinders(..),
  unifyNameBinders,
  andThenUnifyPatterns,
  andThenUnifyNameBinders,
  UnifiablePattern(..),
  UnifiableInPattern(..),
  NameBinders,
  emptyNameBinders,
  mergeNameBinders,
  -- ** Eliminating impossible unification
  V2, absurd2,
  -- * Name maps
  NameMap,
  emptyNameMap,
  lookupName,
  addNameBinder,
  nameMapToSubstitution,
  addNameBinders,
  addNameBinderList,
  NameBinderList(..),
  -- * Constraints
  Ext,
  ExtEvidence(..),
  Distinct,
  DistinctEvidence(..),
  assertDistinct,
  assertExt,
  DExt,
  InjectName(..),
) where

import           Control.Monad.Foil.Internal
