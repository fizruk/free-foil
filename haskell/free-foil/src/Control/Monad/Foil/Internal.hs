{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
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
import           Data.Coerce     (coerce)
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
  deriving newtype (NFData, Eq, Ord, Show)

-- | A name binder is a name that extends scope @n@ to a (larger) scope @l@.
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord, Show)

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

-- | Convert 'Name' into an identifier.
-- This may be useful for printing and debugging.
nameId :: Name l -> Id
nameId (UnsafeName i) = i

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

-- | A distinct scope extended with a 'NameBinder' is also distinct.
assertExt :: NameBinder n l -> ExtEvidence n l
assertExt _ = unsafeExt

-- | Safely rename (if necessary) a given name to extend a given scope.
-- This is similar to 'withFresh', except if the name does not clash with
-- the scope, it can be used immediately, without renaming.
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

newtype WithRefreshedPattern e n l o o' = WithRefreshedPattern (Substitution e n o -> Substitution e l o')

idWithRefreshedPattern :: (Sinkable e, DExt o o') => WithRefreshedPattern e n n o o'
idWithRefreshedPattern = WithRefreshedPattern sink

compWithRefreshedPattern
  :: (DExt o o', DExt o' o'')
  => WithRefreshedPattern e n i o o'
  -> WithRefreshedPattern e i l o' o''
  -> WithRefreshedPattern e n l o o''
compWithRefreshedPattern (WithRefreshedPattern f) (WithRefreshedPattern g) =
  WithRefreshedPattern (g . f)

-- | Safely rename (if necessary) a given pattern to extend a given scope.
-- This is similar to 'withFreshPattern', except if a name in the pattern
-- does not clash with the scope, it can be used immediately, without renaming.
--
-- This is a more general version of 'withRefreshed'.
withRefreshedPattern
  :: (Distinct o, CoSinkable pattern, Sinkable e, InjectName e)
  => Scope o      -- ^ Ambient scope.
  -> pattern n l  -- ^ Pattern to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => (Substitution e n o -> Substitution e l o') -> pattern o o' -> r)
  -- ^ Continuation, accepting the refreshed pattern.
  -> r
withRefreshedPattern scope pattern cont = withPattern
  (\scope' binder f -> withRefreshed scope' (nameOf binder)
    (\binder' -> f (WithRefreshedPattern (\subst -> addRename (sink subst) binder (nameOf binder'))) binder'))
  idWithRefreshedPattern
  compWithRefreshedPattern
  scope
  pattern
  (\(WithRefreshedPattern f) pattern' -> cont f pattern')

-- | Rename a given pattern into a fresh version of it to extend a given scope.
--
-- This is similar to 'withRefreshPattern', except here renaming always takes place.
withFreshPattern
  :: (Distinct o, CoSinkable pattern, Sinkable e, InjectName e)
  => Scope o      -- ^ Ambient scope.
  -> pattern n l  -- ^ Pattern to refresh (if it clashes with the ambient scope).
  -> (forall o'. DExt o o' => (Substitution e n o -> Substitution e l o') -> pattern o o' -> r)
  -- ^ Continuation, accepting the refreshed pattern.
  -> r
withFreshPattern scope pattern cont = withPattern
  (\scope' binder f -> withFresh scope'
    (\binder' -> f (WithRefreshedPattern (\subst -> addRename (sink subst) binder (nameOf binder'))) binder'))
  idWithRefreshedPattern
  compWithRefreshedPattern
  scope
  pattern
  (\(WithRefreshedPattern f) pattern' -> cont f pattern')

newtype WithRefreshedPattern' e n l (o :: S) (o' :: S) = WithRefreshedPattern' ((Name n -> e o) -> Name l -> e o')

idWithRefreshedPattern' :: (Sinkable e, DExt o o') => WithRefreshedPattern' e n n o o'
idWithRefreshedPattern' = WithRefreshedPattern' (\f n -> sink (f n))

compWithRefreshedPattern'
  :: (DExt o o', DExt o' o'')
  => WithRefreshedPattern' e n i o o'
  -> WithRefreshedPattern' e i l o' o''
  -> WithRefreshedPattern' e n l o o''
compWithRefreshedPattern' (WithRefreshedPattern' f) (WithRefreshedPattern' g) =
  WithRefreshedPattern' (g . f)

-- | Refresh (if needed) bound variables introduced in a pattern.
--
-- This is a version of 'withRefreshedPattern' that uses functional renamings instead of 'Substitution'.
withRefreshedPattern'
  :: (CoSinkable pattern, Distinct o, InjectName e, Sinkable e)
  => Scope o
  -> pattern n l
  -> (forall o'. DExt o o' => ((Name n -> e o) -> Name l -> e o') -> pattern o o' -> r) -> r
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
  (\(WithRefreshedPattern' f) pattern' -> cont f pattern')

-- | Try coercing the name back to the (smaller) scope,
-- given a binder that extends that scope.
unsinkName :: NameBinder n l -> Name l -> Maybe (Name n)
unsinkName binder name@(UnsafeName raw)
  | nameOf binder == name = Nothing
  | otherwise = Just (UnsafeName raw)

-- * Unification of binders

-- | Unification result for two binders,
-- extending some common scope to scopes @l@ and @r@ respectively.
--
-- Due to the implementation of the foil,
data UnifyNameBinders n l r where
  -- | Binders are the same, proving that type parameters @l@ and @r@
  -- are in fact equivalent.
  SameNameBinders :: UnifyNameBinders n l l
  -- | It is possible to safely rename the left binder
  -- to match the right one.
  RenameLeftNameBinder :: (NameBinder n l -> NameBinder n r) -> UnifyNameBinders n l r
  -- | It is possible to safely rename the right binder
  -- to match the left one.
  RenameRightNameBinder :: (NameBinder n r -> NameBinder n l) -> UnifyNameBinders n l r

-- | Unify binders either by asserting that they are the same,
-- or by providing a /safe/ renaming function to convert one binder to another.
unifyNameBinders
  :: forall i l r.
     NameBinder i l
  -> NameBinder i r
  -> UnifyNameBinders i l r
unifyNameBinders (UnsafeNameBinder (UnsafeName i1)) (UnsafeNameBinder (UnsafeName i2))
  | i1 == i2  = unsafeCoerce (SameNameBinders @l)  -- equal names extend scopes equally
  | i1 < i2   = RenameRightNameBinder $ \(UnsafeNameBinder (UnsafeName i'')) ->
      if i'' == i2 then UnsafeNameBinder (UnsafeName i1) else UnsafeNameBinder (UnsafeName i'')
  | otherwise = RenameLeftNameBinder $ \(UnsafeNameBinder (UnsafeName i')) ->
      if i'  == i1 then UnsafeNameBinder (UnsafeName i2) else UnsafeNameBinder (UnsafeName i')

-- * Safe sinking

-- | Sinking an expression from scope @n@ into a (usualy extended) scope @l@,
-- given the renaming (injection from scope @n@ to scope @l@).
class Sinkable (e :: S -> Type) where
  -- | An implementation of this method that typechecks
  -- proves to the compiler that the expression is indeed
  -- 'Sinkable'. However, instead of this implementation, 'sink'
  -- should be used at all call sites for efficiency.
  sinkabilityProof
    :: (Name n -> Name l)   -- ^ Map names from scope @n@ to a (possibly larger) scope @l@.
    -> e n                  -- ^ Expression with free variables in scope @n@.
    -> e l

-- | Sinking a 'Name' is as simple as applying the renaming.
instance Sinkable Name where
  sinkabilityProof rename = rename

-- | Efficient version of 'sinkabilityProof'.
-- In fact, once 'sinkabilityProof' typechecks,
-- it is safe to 'sink' by coercion.
-- See Section 3.5 in [«The Foil: Capture-Avoiding Substitution With No Sharp Edges»](https://doi.org/10.1145/3587216.3587224) for the details.
sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

-- | Extend renaming when going under a 'CoSinkable' pattern (generalized binder).
-- Note that the scope under pattern is independent of the codomain of the renaming.
--
-- This function is used to go under binders when implementing 'sinkabilityProof'
-- and is both a generalization of 'extendRenamingNameBinder' and an efficient implementation of 'coSinkabilityProof'.
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
composeNameBinderRenamings
  :: (NameBinder n i -> NameBinder n i')    -- ^ Rename binders extending scope @n@ from @i@ to @i'@.
  -> (NameBinder i' l -> NameBinder i' l')  -- ^ Rename binders extending scope @i'@ from @l@ to @l'@.
  -> (NameBinder n l -> NameBinder n l')
composeNameBinderRenamings = unsafeCoerce (flip (.))

-- | Convert renaming of name binders into renaming of names in the inner scopes.
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

  withPattern
    :: Distinct o
    => (forall x y z r'. Distinct z => Scope z -> NameBinder x y -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r') -> r')
    -> (forall x z z'. DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (DExt z z', DExt z' z'') => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Scope o
    -> pattern n l
    -> (forall o'. DExt o o' => f n l o o' -> pattern o o' -> r) -> r

instance CoSinkable NameBinder where
  coSinkabilityProof _rename (UnsafeNameBinder name) cont =
    cont unsafeCoerce (UnsafeNameBinder name)

  withPattern f _ _ = f

-- * Safe substitions

-- | A substitution is a mapping from names in scope @i@
-- to expressions @e o@ in scope @o@.
newtype Substitution (e :: S -> Type) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (e o))

-- | Apply substitution to a given name.
lookupSubst :: InjectName e => Substitution e i o -> Name i -> e o
lookupSubst (UnsafeSubstitution env) (UnsafeName name) =
    case IntMap.lookup name env of
        Just ex -> ex
        Nothing -> injectName (UnsafeName name)

-- | Identity substitution maps all names to expresion-variables.
identitySubst
  :: InjectName e => Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

-- | Extend substitution with a particular mapping.
addSubst
  :: Substitution e i o
  -> NameBinder i i'
  -> e o
  -> Substitution e i' o
addSubst (UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName name)) ex
  = UnsafeSubstitution (IntMap.insert name ex env)

-- | Add variable renaming to a substitution.
-- This includes the performance optimization of eliding names mapped to themselves.
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
newtype NameMap (n :: S) a = NameMap { getNameMap :: IntMap a }

-- | An empty map belongs in the empty scope.
emptyNameMap :: NameMap VoidS a
emptyNameMap = NameMap IntMap.empty

-- | Looking up a name should always succeed.
--
-- Note that since 'Name' is 'Sinkable', you can lookup a name from scope @n@ in a 'NameMap' for scope @l@ whenever @l@ extends @n@.
lookupName :: Name n -> NameMap n a -> a
lookupName name (NameMap m) =
  case IntMap.lookup (nameId name) m of
    Nothing -> error "impossible: unknown name in a NameMap"
    Just x  -> x

-- | Extending a map with a single mapping.
--
-- Note that the scope parameter of the result differs from the initial map.
addNameBinder :: NameBinder n l -> a -> NameMap n a -> NameMap l a
addNameBinder name x (NameMap m) = NameMap (IntMap.insert (nameId (nameOf name)) x m)

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

-- | Check if a raw name is contained in a raw scope.
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

-- | Instances of this typeclass possess the ability to inject names.
-- Usually, this is a variable data constructor.
class InjectName (e :: S -> Type) where
  -- | Inject names into expressions.
  injectName :: Name n -> e n
