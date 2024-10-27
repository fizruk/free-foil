{-# OPTIONS_GHC -Wno-missing-methods #-}
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
module Control.Monad.Free.Foil.Generic where

import           Data.Kind              (Constraint, Type)
import           Generics.Kind
import           Generics.Kind.Examples ()
import           GHC.TypeError

type ZipLoT :: LoT k -> LoT k -> LoT k
type family ZipLoT as bs where
  ZipLoT LoT0 LoT0 = LoT0
  ZipLoT (a :&&: as) (b :&&: bs) = ((a, b) :&&: ZipLoT as bs)

type Mappings :: LoT k -> LoT k -> LoT k -> Type
data Mappings (as :: LoT k) (bs :: LoT k) (cs :: LoT k) where
  M0 :: Mappings LoT0 LoT0 LoT0
  (:^:) :: (a -> b -> Maybe c) -> Mappings as bs cs -> Mappings (a :&&: as) (b :&&: bs) (c :&&: cs)

class PairMappings (as :: LoT k) (bs :: LoT k) where
  pairMappings :: Mappings as bs (ZipLoT as bs)

instance PairMappings LoT0 LoT0 where
  pairMappings = M0

instance PairMappings as bs => PairMappings ((a :: Type) :&&: as) ((b :: Type) :&&: bs) where
  pairMappings = (\x y -> Just (x, y)) :^: pairMappings

class ApplyMappings (v :: TyVar d Type) where
  applyMappings :: forall (as :: LoT d) (bs :: LoT d) (cs :: LoT d).
    Mappings as bs cs -> Interpret (Var v) as -> Interpret (Var v) bs -> Maybe (Interpret (Var v) cs)

instance ApplyMappings (VZ :: TyVar (Type -> tys) Type) where
  applyMappings (f :^: _) x y = f x y

instance ApplyMappings v => ApplyMappings (VS v :: TyVar (ty -> tys) Type) where
  applyMappings (_ :^: fs) x y = applyMappings @_ @v fs x y

genericZipMatchK :: forall f as bs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatch (RepK f) as bs, PairMappings as bs)
    => f :@@: as -> f :@@: bs -> Maybe (f :@@: (ZipLoT as bs))
genericZipMatchK = genericZipMatchWithK @f @as @bs pairMappings

genericZipMatchWithK :: forall f as bs cs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatchWith (RepK f) as bs cs)
    => Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
genericZipMatchWithK mappings x y = toK @_ @f @cs <$> gzipMatchWith mappings
  (fromK @_ @f @as x)
  (fromK @_ @f @bs y)

genericZipMatch2
   :: forall sig scope scope' term term'.
   (GenericK sig, GZipMatch (RepK sig), ReqsZipMatch (RepK sig) (scope :&&: term :&&: 'LoT0) (scope' :&&: term' :&&: 'LoT0))
   => sig scope term -> sig scope' term' -> Maybe (sig (scope, scope') (term, term'))
genericZipMatch2 = genericZipMatchK @sig @(scope :&&: term :&&: 'LoT0) @(scope' :&&: term' :&&: 'LoT0)

zipMatchK :: forall f as bs. (ZipMatchK f, PairMappings as bs) => f :@@: as -> f :@@: bs -> Maybe (f :@@: ZipLoT as bs)
zipMatchK = zipMatchWithK @_ @f @as @bs pairMappings

class ZipMatchK (f :: k) where
  zipMatchWithK :: forall as bs cs. Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
  default zipMatchWithK :: forall as bs cs.
    (GenericK f, GZipMatch (RepK f), ReqsZipMatchWith (RepK f) as bs cs)
    => Mappings as bs cs -> f :@@: as -> f :@@: bs -> Maybe (f :@@: cs)
  zipMatchWithK = genericZipMatchWithK @f @as @bs @cs

zipMatchViaEq :: Eq a => Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaEq _ x y
  | x == y = Just x
  | otherwise = Nothing

zipMatchViaChooseLeft :: Mappings as bs cs -> a -> a -> Maybe a
zipMatchViaChooseLeft _ x _ = Just x

-- instance ZipMatchK (,)     -- missing GenericK instance upstream
instance ZipMatchK []
instance ZipMatchK Maybe
instance ZipMatchK Either
instance ZipMatchK a => ZipMatchK (Either a)

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

instance (ZipMatchFields t, ZipMatchK k) => ZipMatchFields (Kon k :@: t) where
  type ReqsZipMatchFieldsWith (Kon k :@: t) as bs cs = ReqsZipMatchFieldsWith t as bs cs

  zipMatchFieldsWith :: forall as bs cs. ReqsZipMatchFieldsWith (Kon k :@: t) as bs cs =>
    Mappings as bs cs -> Field (Kon k :@: t) as -> Field (Kon k :@: t) bs -> Maybe (Field (Kon k :@: t) cs)
  zipMatchFieldsWith g (Field l) (Field r) =
    Field <$> zipMatchWithK @_ @k @(Interpret t as :&&: LoT0) @(Interpret t bs :&&: LoT0) @(Interpret t cs :&&: LoT0)
      ((\ll rr -> unField @t <$> zipMatchFieldsWith g (Field ll) (Field rr)) :^: M0) l r

instance (ZipMatchFields t1, ZipMatchFields t2, ZipMatchK k) => ZipMatchFields ((Kon k :@: t1) :@: t2) where
  type ReqsZipMatchFieldsWith ((Kon k :@: t1) :@: t2) as bs cs = (ReqsZipMatchFieldsWith t1 as bs cs, ReqsZipMatchFieldsWith t2 as bs cs)

  zipMatchFieldsWith :: forall as bs cs. ReqsZipMatchFieldsWith ((Kon k :@: t1) :@: t2) as bs cs =>
    Mappings as bs cs -> Field ((Kon k :@: t1) :@: t2) as -> Field ((Kon k :@: t1) :@: t2) bs -> Maybe (Field ((Kon k :@: t1) :@: t2) cs)
  zipMatchFieldsWith g (Field l) (Field r) =
    Field <$> zipMatchWithK @_ @k @(Interpret t1 as :&&: Interpret t2 as :&&: LoT0) @(Interpret t1 bs :&&: Interpret t2 bs :&&: LoT0) @(Interpret t1 cs :&&: Interpret t2 cs :&&: LoT0)
      ((\ll rr -> unField @t1 <$> zipMatchFieldsWith g (Field ll) (Field rr))
        :^: ((\ll rr -> unField @t2 <$> zipMatchFieldsWith g (Field ll) (Field rr))
        :^: M0)) l r

instance {-# OVERLAPPABLE #-} TypeError ('Text "Atom :@: is not supported by ZipMatchFields is a general form") => ZipMatchFields (f :@: t) where
  -- type ReqsZipMatchFieldsWith (f :@: t) as bs cs = TypeError ('Text "Atom :@: is not supported by ZipMatchFields is a general form")
  zipMatchFieldsWith = undefined

instance TypeError ('Text "Atom ForAll is not supported by ZipMatchFields") => ZipMatchFields (ForAll a) where
  type ReqsZipMatchFieldsWith (ForAll a) as bs cs = TypeError ('Text "Atom ForAll is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined
instance TypeError ('Text "Atom :=>>: is not supported by ZipMatchFields") => ZipMatchFields (c :=>>: a) where
  type ReqsZipMatchFieldsWith (c :=>>: a) as bs cs = TypeError ('Text "Atom :=>>: is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined
instance TypeError ('Text "Atom Eval is not supported by ZipMatchFields") => ZipMatchFields (Eval a) where
  type ReqsZipMatchFieldsWith (Eval a) as bs cs = TypeError ('Text "Atom Eval is not supported by ZipMatchFields")
  zipMatchFieldsWith = undefined

-- instance ZipMatchFields (ForAll f) where
--   type ReqsZipMatchFields (ForAll f) as bs = ???
--   zipMatchFields = ???

-- instance ZipMatchFields (c :=>>: f) where
--   type ReqsZipMatchFields (c :=>>: f) as bs = ???
--   zipMatchFields = ???

-- instance ZipMatchFields (Eval f) where
--   type ReqsZipMatchFields (Eval f) as bs = ???
--   zipMatchFields = ???
