{-# LANGUAGE StandaloneKindSignatures  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE DataKinds  #-}
module Control.Monad.Foil.Internal.ValidNameBinders where

import Data.Kind (Type, Constraint)
import GHC.TypeError
import GHC.TypeLits
import Generics.Kind
import qualified GHC.Generics as GHC

type SubstInRepK :: TyVar d k -> Atom d k -> (LoT d -> Type) -> LoT d -> Type
type family SubstInRepK i atom f where
  SubstInRepK i atom V1 = V1
  SubstInRepK i atom U1 = U1
  SubstInRepK i atom (M1 info c f) = M1 info c (SubstInRepK i atom f)
  SubstInRepK i atom (Field field) = Field (SubstInAtom i atom field)
  SubstInRepK i atom f =
    TypeError
      ('Text "cannot substitute variable"
      :$$: 'Text "  " :<>: 'ShowType (Var i)
      :$$: 'Text "with atom"
      :$$: 'Text "  " :<>: 'ShowType atom
      :$$: 'Text "in"
      :$$: 'Text "  " :<>: 'ShowType f)

type SubstInAtom :: TyVar d k -> Atom d k -> Atom d k1 -> Atom d k1
type family SubstInAtom i atom f where
  SubstInAtom i atom (Var i) = atom
  SubstInAtom i atom (Var j) = Var j
  SubstInAtom i atom (Kon a) = Kon a
  SubstInAtom i atom (f :@: x) = SubstInAtom i atom f :@: SubstInAtom i atom x
  -- SubstInAtom i atom atom' = atom'
  SubstInAtom i atom atom' =
    TypeError
      ('Text "cannot substitute variable"
      :$$: 'Text "  " :<>: 'ShowType (Var i)
      :$$: 'Text "with atom"
      :$$: 'Text "  " :<>: 'ShowType atom
      :$$: 'Text "in an atom"
      :$$: 'Text "  " :<>: 'ShowType atom')

type ShowKindedScope oo n ll = ShowScope oo n ll :<>: 'Text " : S"

type ShowScope :: Atom d s -> Atom d s -> Atom d s -> ErrorMessage
type family ShowScope oo n ll where
  ShowScope oo ll ll = 'Text "innerScope"
  ShowScope oo oo ll = 'Text "outerScope"
  ShowScope oo n  ll = ShowScopeN 1 n

type ShowScopeN :: Natural -> Atom d s -> ErrorMessage
type family ShowScopeN i n where
  ShowScopeN i (Var VZ) = 'Text "scope" :<>: 'ShowType i
  ShowScopeN i (Var (VS x)) = ShowScopeN (i + 1) (Var x)

type ShowSaturatedPatternType pattern oo n l ll =
  'ShowType pattern :<>: 'Text " " :<>: ShowScope oo n ll :<>: 'Text " " :<>: ShowScope oo l ll

type GInnerScopeOfAtom :: ErrorMessage -> Nat -> Nat -> (s -> s -> Type) -> Atom d Type -> Atom d s -> Atom d s -> Atom d s -> Atom d s
type family GInnerScopeOfAtom msg icon ifield pattern atom oo n ll where
  GInnerScopeOfAtom msg icon ifield pattern (Kon a) oo n ll = n
  GInnerScopeOfAtom msg icon ifield pattern (Kon f :@: n :@: l) oo n ll = l
  GInnerScopeOfAtom msg icon ifield pattern (Kon f :@: o :@: i) oo n ll =
    TypeError
      ('Text "Unexpected Foil scope extension in the binder/pattern"
      :$$: 'Text "  " :<>: ShowSaturatedPatternType f oo o i ll
      :$$: 'Text "the binder/pattern tries to extend scope"
      :$$: 'Text "  " :<>: ShowKindedScope oo o ll
      :$$: 'Text "to scope"
      :$$: 'Text "  " :<>: ShowKindedScope oo i ll
      :$$: 'Text "but it is expected to extend the current (outer) scope"
      :$$: 'Text "  " :<>: ShowKindedScope oo n ll
      :$$: ShowLocalizeError msg icon ifield pattern oo ll
      )
  GInnerScopeOfAtom msg icon ifield pattern atom oo n ll =
    TypeError
      ('Text "the following atom does not seem to be a valid part of a pattern/binder"
      :$$: 'Text "  " :<>: 'ShowType atom
      :$$: ShowLocalizeError msg icon ifield pattern oo ll)

type SameInnerScope :: ErrorMessage -> Nat -> (s -> s -> Type) -> Atom k s -> Atom k s -> Atom k s
type family SameInnerScope msg icon pattern n l where
  SameInnerScope msg icon pattern l l = l
  SameInnerScope msg icon pattern n l =
    TypeError
      ('Text "Unexpected extended (inner) Foil scope in the data type"
      :$$: 'Text "  " :<>: ShowSaturatedPatternType pattern n n l l
      :$$: 'Text "expecting extended (inner) scope to be"
      :$$: 'Text "  " :<>: ShowKindedScope n l l
      :$$: 'Text "but the inferred extended (inner) scope is"
      :$$: 'Text "  " :<>: ShowKindedScope n n l
      :$$: ShowLocalizeError msg icon 0 pattern n l
      )

type GValidNameBinders :: (s -> s -> Type) -> (LoT (s -> s -> Type) -> Type) -> Constraint
type family GValidNameBinders pattern f :: Constraint where
  GValidNameBinders pattern (f :: LoT (s -> s -> Type) -> Type) =
    (GInnerScopeOfRepK ('Text "") 0 0 pattern f Var0 Var0 Var1)
    ~ (Var1 :: Atom (s -> s -> Type) s)

type AtomSucc :: Atom d k1 -> Atom (k -> d) k1
type family AtomSucc atom where
  AtomSucc (Var i) = Var (VS i)

type AtomUnSucc :: ErrorMessage -> Nat -> (s -> s -> Type) -> Atom d s -> Atom d s -> Atom (k -> d) k1 -> Atom d k1
type family AtomUnSucc msg icon pattern oo ll atom where
  AtomUnSucc msg icon pattern oo ll (Var (VS i)) = Var i
  AtomUnSucc msg icon pattern oo ll (Var VZ) = TypeError
    ('Text "Intermediate scope escapes existential quantification for data type"
      :$$: ShowLocalizeError msg icon 0 pattern oo ll
      )

type family First x y where
  First (Var x) (Var y) = Var x

type family AndShowFieldNumber ifield msg where
  AndShowFieldNumber 0 msg = msg
  AndShowFieldNumber n msg =
    'Text "when checking field number " :<>: 'ShowType n
    :$$: msg

type family AndShowConNumber icon msg where
  AndShowConNumber 0 msg = msg
  AndShowConNumber n msg =
    'Text "when checking constructor number " :<>: 'ShowType n
    :$$: msg

type AndShowDataType pattern n l msg =
  'Text "when tracking Foil scopes for the data type"
  :$$: 'Text "  " :<>: ShowSaturatedPatternType pattern n n l l
  :$$: msg

type ShowLocalizeError msg icon ifield pattern o l =
    AndShowFieldNumber ifield
      (AndShowConNumber icon
        (AndShowDataType pattern o l
          msg))

type family CountCons f where
  CountCons (f :+: g) = CountCons f + CountCons g
  CountCons (M1 GHC.C c f) = 1

type family CountFields f where
  CountFields (f :*: g) = CountFields f + CountFields g
  CountFields (M1 GHC.S c f) = 1

type GInnerScopeOfRepK :: ErrorMessage -> Nat -> Nat -> (s -> s -> Type) -> (LoT k -> Type) -> Atom k s -> Atom k s -> Atom k s -> Atom k s
type family GInnerScopeOfRepK msg icon ifield pattern f o n l where
  GInnerScopeOfRepK msg icon ifield pattern V1 o n l = l
  GInnerScopeOfRepK msg icon ifield pattern U1 o n l = n
  GInnerScopeOfRepK msg icon ifield pattern (M1 GHC.C c f) o n l =
    GInnerScopeOfRepK msg icon 1 pattern f o n l
  GInnerScopeOfRepK msg icon ifield pattern (M1 GHC.D c f) o n l =
    GInnerScopeOfRepK msg 1 ifield pattern f o n l
  GInnerScopeOfRepK msg icon ifield pattern (M1 i c f) o n l =
    GInnerScopeOfRepK msg icon ifield pattern f o n l
  GInnerScopeOfRepK msg icon ifield pattern (f :+: g) o n l = First
    (SameInnerScope msg icon pattern (GInnerScopeOfRepK msg icon ifield pattern f o n l) l)
    (SameInnerScope msg icon pattern (GInnerScopeOfRepK msg (icon + CountCons f) ifield pattern g o n l) l)
  GInnerScopeOfRepK msg icon ifield pattern (f :*: g) o n l =
    GInnerScopeOfRepK msg icon (ifield + CountFields f) pattern g o
      (GInnerScopeOfRepK msg icon ifield pattern f o n l) l
  GInnerScopeOfRepK msg icon ifield pattern (Var i :~~: Var j :=>: f) o n l =
    GInnerScopeOfRepK msg icon ifield pattern (SubstInRepK i (Var j) f)
      (SubstInAtom i (Var j) o) (SubstInAtom i (Var j) n) (SubstInAtom i (Var j) l)
  GInnerScopeOfRepK msg icon ifield pattern (Exists k f) o n l =
    AtomUnSucc msg icon pattern o l
      (GInnerScopeOfRepK msg icon ifield pattern f (AtomSucc o) (AtomSucc n) (AtomSucc l))
  GInnerScopeOfRepK msg icon ifield pattern (Field atom) o n l = GInnerScopeOfAtom msg icon ifield pattern atom o n l
  GInnerScopeOfRepK msg icon ifield pattern f o n l =
    TypeError
      ('Text "Unsupported structure in a binder/pattern"
      :$$: 'Text "  " :<>: 'ShowType f
      :$$: ShowLocalizeError msg icon 0 pattern n l)
