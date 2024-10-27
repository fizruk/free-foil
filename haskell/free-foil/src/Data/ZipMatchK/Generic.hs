{-# OPTIONS_GHC -Wno-missing-methods -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
module Data.ZipMatchK.Generic where

import           Data.Kind              (Constraint, Type)
import           Data.List.NonEmpty
import           Generics.Kind
import           Generics.Kind.Examples ()
import           GHC.TypeError
import           Data.ZipMatchK.Mappings

-- | Kind-polymorphic syntactic (first-order) unification of two values.
--
-- Note: @f@ is expected to be a traversable n-functor,
-- but at the moment we lack a @TraversableK@ constraint.
class ZipMatchK (f :: k) where
  -- | Perform one level of equality testing:
  --
  -- * when @k = 'Type'@, values are compared directly (e.g. via 'Eq');
  -- * when @k = 'Type' -> 'Type'@, we compare term constructors;
  --   if term constructors are unequal, we return 'Nothing';
  --   otherwise, we pair up all components with a given function.
  zipMatchWithK :: forall as bs cs. Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
  default zipMatchWithK :: forall as bs cs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatchWith (RepK f) as bs cs)
    => Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
  zipMatchWithK = genericZipMatchWithK @f @as @bs @cs

-- | Generic implementation of 'Data.ZipMatch.zipMatchK'.
genericZipMatchK :: forall f as bs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatch (RepK f) as bs, PairMappings as bs)
    => f :@@: as -> f :@@: bs -> Maybe (f :@@: (ZipLoT as bs))
genericZipMatchK = genericZipMatchWithK @f @as @bs pairMappings

-- | Generic implementation of 'zipMatchWithK'.
genericZipMatchWithK :: forall f as bs cs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatchWith (RepK f) as bs cs)
    => Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
genericZipMatchWithK mappings x y = toK @_ @f @cs <$> gzipMatchWith mappings
  (fromK @_ @f @as x)
  (fromK @_ @f @bs y)

instance GenericK (,) where
  type RepK (,) = Field Var0 :*: Field Var1
instance GenericK ((,) a) where
  type RepK ((,) a) = Field (Kon a) :*: Field Var0
instance GenericK NonEmpty where
  type RepK NonEmpty = Field Var0 :*: Field ([] :$: Var0)

instance ZipMatchK (,)
instance ZipMatchK a => ZipMatchK ((,) a)
instance ZipMatchK []
instance ZipMatchK Maybe
instance ZipMatchK Either
instance ZipMatchK a => ZipMatchK (Either a)
instance ZipMatchK NonEmpty

type ReqsZipMatch f as bs = ReqsZipMatchWith f as bs (ZipLoT as bs)
class GZipMatch (f :: LoT k -> Type) where
  type ReqsZipMatchWith f (as :: LoT k) (bs :: LoT k) (cs :: LoT k) :: Constraint
  gzipMatchWith :: ReqsZipMatchWith f as bs cs => Mappings as bs cs -> f as -> f bs -> Maybe (f cs)

instance GZipMatch V1 where
  type ReqsZipMatchWith V1 as bs cs = ()
  gzipMatchWith _ _ _ = error "impossible: Generics.Kind.V1 value!" -- FIXME: should be absurd

instance GZipMatch U1 where
  type ReqsZipMatchWith U1 as bs cs = ()
  gzipMatchWith _ U1 U1 = Just U1

instance GZipMatch f => GZipMatch (M1 i c f) where
  type ReqsZipMatchWith (M1 i c f) as bs cs = ReqsZipMatchWith f as bs cs
  gzipMatchWith g (M1 x) (M1 y) = M1 <$> gzipMatchWith g x y

instance (GZipMatch f, GZipMatch g) => GZipMatch (f :+: g) where
  type ReqsZipMatchWith (f :+: g) as bs cs = (ReqsZipMatchWith f as bs cs, ReqsZipMatchWith g as bs cs)
  gzipMatchWith g (L1 x) (L1 y) = L1 <$> gzipMatchWith g x y
  gzipMatchWith g (R1 x) (R1 y) = R1 <$> gzipMatchWith g x y
  gzipMatchWith _ _ _           = Nothing

instance (GZipMatch f, GZipMatch g) => GZipMatch (f :*: g) where
  type ReqsZipMatchWith (f :*: g) as bs cs = (ReqsZipMatchWith f as bs cs, ReqsZipMatchWith g as bs cs)
  gzipMatchWith g (x :*: y) (x' :*: y') =
    liftA2 (:*:) (gzipMatchWith g x x') (gzipMatchWith g y y')

instance ZipMatchFields t => GZipMatch (Field t) where
  type ReqsZipMatchWith (Field t) as bs cs = ReqsZipMatchFieldsWith t as bs cs
  gzipMatchWith f x y = zipMatchFieldsWith f x y

instance GZipMatch f => GZipMatch (c :=>: f) where
  type ReqsZipMatchWith (c :=>: f) as bs cs = (ReqsZipMatchWith f as bs cs, Interpret c cs)
  -- really we want          = (Interpret c as, Interpret c bs) => (ReqsZipMatch f as bs, Interpret c (ZipLoT as bs))
  gzipMatchWith g (SuchThat x) (SuchThat y) = SuchThat <$> gzipMatchWith g x y

instance TypeError ('Text "Existentials are not supported")
         => GZipMatch (Exists k f) where
  type ReqsZipMatchWith (Exists k f) as bs cs = TypeError ('Text "Existentials are not supported")
  gzipMatchWith = undefined

class ZipMatchFields (t :: Atom d Type) where
  type ReqsZipMatchFieldsWith t (as :: LoT d) (bs :: LoT d) (cs :: LoT d) :: Constraint
  zipMatchFieldsWith :: ReqsZipMatchFieldsWith t as bs cs => Mappings as bs cs -> Field t as -> Field t bs -> Maybe (Field t cs)

instance ApplyMappings v => ZipMatchFields (Var v) where
  -- this is always true, but GHC is not smart enough to know that, I think
  type ReqsZipMatchFieldsWith (Var v) as bs cs = () -- InterpretVar v cs ~ (InterpretVar v as, InterpretVar v bs))
  zipMatchFieldsWith g (Field x) (Field y) = Field <$> applyMappings @_ @v g x y

instance ZipMatchK k => ZipMatchFields (Kon k) where
  type ReqsZipMatchFieldsWith (Kon k) as bs cs = ()
  zipMatchFieldsWith _ (Field l) (Field r) = Field <$> zipMatchWithK @_ @k M0 l r

instance {-# OVERLAPPING #-} (ZipMatchFields t, ZipMatchK k) => ZipMatchFields (Kon k :@: t) where
  type ReqsZipMatchFieldsWith (Kon k :@: t) as bs cs = ReqsZipMatchFieldsWith t as bs cs

  zipMatchFieldsWith :: forall as bs cs. ReqsZipMatchFieldsWith (Kon k :@: t) as bs cs =>
    Mappings as bs cs -> Field (Kon k :@: t) as -> Field (Kon k :@: t) bs -> Maybe (Field (Kon (k :: Type -> Type) :@: t) cs)
  zipMatchFieldsWith g (Field l) (Field r) =
    Field <$> zipMatchWithK @_ @k @(Interpret t as :&&: LoT0) @(Interpret t bs :&&: LoT0) @(Interpret t cs :&&: LoT0)
      ((\ll rr -> unField @t <$> zipMatchFieldsWith g (Field ll) (Field rr)) :^: M0) l r

instance {-# OVERLAPPING #-} (ZipMatchFields t1, ZipMatchFields t2, ZipMatchK k) => ZipMatchFields ((Kon (k :: Type -> Type -> Type) :@: t1) :@: t2) where
  type ReqsZipMatchFieldsWith ((Kon k :@: t1) :@: t2) as bs cs = (ReqsZipMatchFieldsWith t1 as bs cs, ReqsZipMatchFieldsWith t2 as bs cs)

  zipMatchFieldsWith :: forall as bs cs. ReqsZipMatchFieldsWith ((Kon k :@: t1) :@: t2) as bs cs =>
    Mappings as bs cs -> Field ((Kon k :@: t1) :@: t2) as -> Field ((Kon k :@: t1) :@: t2) bs -> Maybe (Field ((Kon k :@: t1) :@: t2) cs)
  zipMatchFieldsWith g (Field l) (Field r) =
    Field <$> zipMatchWithK @_ @k @(Interpret t1 as :&&: Interpret t2 as :&&: LoT0) @(Interpret t1 bs :&&: Interpret t2 bs :&&: LoT0) @(Interpret t1 cs :&&: Interpret t2 cs :&&: LoT0)
      ((\ll rr -> unField @t1 <$> zipMatchFieldsWith g (Field ll) (Field rr))
        :^: ((\ll rr -> unField @t2 <$> zipMatchFieldsWith g (Field ll) (Field rr))
        :^: M0)) l r

instance {-# OVERLAPPABLE #-} TypeError
  ('Text "The type constructor is kind-polymorphic:"
  :$$: 'Text "  " :<>: 'ShowType k :<>: 'Text " : " :<>: 'ShowType (kk -> Type)
  :$$: 'Text "Possible fix:"
  :$$: 'Text "  add an explicit kind signature"
  :$$: 'Text "    " :<>: 'ShowType k :<>: 'Text " : " :<>: 'ShowType (Type -> Type))
  => ZipMatchFields (Kon (k :: kk -> Type) :@: t) where
  zipMatchFieldsWith = undefined

instance {-# OVERLAPPABLE #-} TypeError
  ('Text "The type constructor is kind-polymorphic:"
  :$$: 'Text "  " :<>: 'ShowType k :<>: 'Text " : " :<>: 'ShowType (kk1 -> kk2 -> Type)
  :$$: 'Text "Possible fix:"
  :$$: 'Text "  add an explicit kind signature"
  :$$: 'Text "    " :<>: 'ShowType k :<>: 'Text " : " :<>: 'ShowType (Type -> Type -> Type))
  => ZipMatchFields ((Kon (k :: kk1 -> kk2 -> Type) :@: t1) :@: t2) where
  zipMatchFieldsWith = undefined

instance {-# OVERLAPPABLE #-} TypeError
  ('Text "Atom :@: is not supported by ZipMatchFields is a general form:"
  :$$: 'Text "  when attempting to use a generic instance for"
  :$$: 'ShowType (f :@: t)
  :$$: 'ShowType f :<>: 'Text " : " :<>: 'ShowType (Atom d (k1 -> Type)))
  => ZipMatchFields ((f :: Atom d (k1 -> Type)) :@: t) where
  -- type ReqsZipMatchFieldsWith (f :@: t) as bs cs = TypeError ('Text "Atom :@: is not supported by ZipMatchFields is a general form")
  zipMatchFieldsWith = undefined

instance TypeError
  ('Text "Atom ForAll is not supported by ZipMatchFields"
  :$$: 'Text "  when attempting to use a generic instance for"
  :$$: 'ShowType (ForAll a)) => ZipMatchFields (ForAll a) where
  type ReqsZipMatchFieldsWith (ForAll a) as bs cs = TypeError ('Text "Atom ForAll is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined
instance TypeError
  ('Text "Atom :=>>: is not supported by ZipMatchFields"
  :$$: 'Text "  when attempting to use a generic instance for"
  :$$: 'ShowType (c :=>>: a)) => ZipMatchFields (c :=>>: a) where
  type ReqsZipMatchFieldsWith (c :=>>: a) as bs cs = TypeError ('Text "Atom :=>>: is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined
instance TypeError
  ('Text "Atom Eval is not supported by ZipMatchFields"
  :$$: 'Text "  when attempting to use a generic instance for"
  :$$: 'ShowType (Eval a)) => ZipMatchFields (Eval a) where
  type ReqsZipMatchFieldsWith (Eval a) as bs cs = TypeError ('Text "Atom Eval is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined
