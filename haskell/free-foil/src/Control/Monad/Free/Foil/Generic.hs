{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
module Control.Monad.Free.Foil.Generic where

import           Data.Kind     (Constraint, Type)
import           Generics.Kind
import           GHC.TypeError

type ZipLoT :: LoT k -> LoT k -> LoT k
type family ZipLoT as bs where
  ZipLoT LoT0 LoT0 = LoT0
  ZipLoT (a :&&: as) (b :&&: bs) = ((a, b) :&&: ZipLoT as bs)

genericZipMatch2
  :: forall sig scope scope' term term'.
  (GenericK sig, GZipMatch (RepK sig), ReqsZipMatch (RepK sig) (scope :&&: term :&&: 'LoT0) (scope' :&&: term' :&&: 'LoT0))
  => sig scope term -> sig scope' term' -> Maybe (sig (scope, scope') (term, term'))
genericZipMatch2 x y = toK <$> gzipMatch
  (fromK @_ @sig @(scope :&&: term :&&: 'LoT0) x)
  (fromK @_ @sig @(scope' :&&: term' :&&: 'LoT0) y)

class GZipMatch (f :: LoT k -> Type) where
  type ReqsZipMatch f (as :: LoT k) (bs :: LoT k) :: Constraint
  gzipMatch :: ReqsZipMatch f as bs => f as -> f bs -> Maybe (f (ZipLoT as bs))

instance GZipMatch V1 where
  type ReqsZipMatch V1 as bs = ()
  gzipMatch _ _ = error "impossible: Generics.Kind.V1 value!" -- FIXME: should be absurd

instance GZipMatch U1 where
  type ReqsZipMatch U1 as bs = ()
  gzipMatch U1 U1 = Just U1

instance GZipMatch f => GZipMatch (M1 i c f) where
  type ReqsZipMatch (M1 i c f) as bs = ReqsZipMatch f as bs
  gzipMatch (M1 x) (M1 y) = M1 <$> gzipMatch x y

instance (GZipMatch f, GZipMatch g) => GZipMatch (f :+: g) where
  type ReqsZipMatch (f :+: g) as bs = (ReqsZipMatch f as bs, ReqsZipMatch g as bs)
  gzipMatch (L1 x) (L1 y) = L1 <$> gzipMatch x y
  gzipMatch (R1 x) (R1 y) = R1 <$> gzipMatch x y
  gzipMatch _ _           = Nothing

instance (GZipMatch f, GZipMatch g) => GZipMatch (f :*: g) where
  type ReqsZipMatch (f :*: g) as bs = (ReqsZipMatch f as bs, ReqsZipMatch g as bs)
  gzipMatch (x :*: y) (x' :*: y') =
    liftA2 (:*:) (gzipMatch x x') (gzipMatch y y')

instance ZipMatchFields t => GZipMatch (Field t) where
  type ReqsZipMatch (Field t) as bs = ReqsZipMatchFields t as bs
  gzipMatch x y = Just (zipMatchFields x y)

instance GZipMatch f => GZipMatch (c :=>: f) where
  type ReqsZipMatch (c :=>: f) as bs = (ReqsZipMatch f as bs, Interpret c (ZipLoT as bs))
  -- really we want          = (Interpret c as, Interpret c bs) => (ReqsZipMatch f as bs, Interpret c (ZipLoT as bs))
  gzipMatch (SuchThat x) (SuchThat y) = SuchThat <$> gzipMatch x y

instance TypeError ('Text "Existentials are not supported")
         => GZipMatch (Exists k f) where
  type ReqsZipMatch (Exists k f) as bs = TypeError ('Text "Existentials are not supported")
  gzipMatch = undefined

class ZipMatchFields t where
  type ReqsZipMatchFields t (as :: LoT k) (bs :: LoT k) :: Constraint
  zipMatchFields :: ReqsZipMatchFields t as bs => Field t as -> Field t bs -> Field t (ZipLoT as bs)

instance ZipMatchFields (Var v) where
  -- this is always true, but GHC is not smart enough to know that, I think
  type ReqsZipMatchFields (Var v) as bs = (InterpretVar v (ZipLoT as bs) ~ (InterpretVar v as, InterpretVar v bs))
  zipMatchFields (Field x) (Field y) = Field (x, y)

instance ZipMatchFields (Kon k) where
  type ReqsZipMatchFields (Kon k) as bs = ()
  zipMatchFields (Field l) _ = Field l

-- instance ZipMatchFields (f :@: x) where
--   type ReqsZipMatchFields (f :@: x) as bs = ???
--   zipMatchFields = ???

-- instance ZipMatchFields (ForAll f) where
--   type ReqsZipMatchFields (ForAll f) as bs = ???
--   zipMatchFields = ???

-- instance ZipMatchFields (c :=>>: f) where
--   type ReqsZipMatchFields (c :=>>: f) as bs = ???
--   zipMatchFields = ???

-- instance ZipMatchFields (Eval f) where
--   type ReqsZipMatchFields (Eval f) as bs = ???
--   zipMatchFields = ???
