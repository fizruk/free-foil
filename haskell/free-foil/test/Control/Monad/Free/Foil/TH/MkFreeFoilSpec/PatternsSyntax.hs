{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-missing-signatures -Wno-redundant-constraints -Wno-orphans #-}

-- | The scope-safe syntax generated from
-- "Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsConfig". The pattern
-- instances other than 'Foil.CoSinkable' take their "Generics.Kind" defaults.
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsSyntax where

import qualified Control.Monad.Foil                                       as Foil
import           Control.Monad.Free.Foil.TH.MkFreeFoil
import           Data.Bifunctor.TH
import           Data.ZipMatchK
import           Generics.Kind.TH                                         (deriveGenericK)

import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsConfig

mkFreeFoil patternsConfig

deriveGenericK ''FFMPattern
instance Foil.SinkableK FFMPattern
instance Foil.HasNameBinders FFMPattern
instance Foil.UnifiablePattern FFMPattern

deriveGenericK ''FFAPattern
instance Foil.SinkableK FFAPattern
instance Foil.HasNameBinders FFAPattern
instance Foil.UnifiablePattern FFAPattern

deriveGenericK ''FFNPattern
instance Foil.SinkableK FFNPattern
instance Foil.HasNameBinders FFNPattern
instance Foil.UnifiablePattern FFNPattern

deriveBifunctor ''MTermSig
deriveBifoldable ''MTermSig
deriveBitraversable ''MTermSig
deriveGenericK ''MTermSig
instance ZipMatchK MTermSig

deriveBifunctor ''ATermSig
deriveBifoldable ''ATermSig
deriveBitraversable ''ATermSig

deriveBifunctor ''NTermSig
deriveBifoldable ''NTermSig
deriveBitraversable ''NTermSig

mkFreeFoilConversions conversionsConfig
