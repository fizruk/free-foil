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
-- Generated conversions carry a redundant @Ord@ constraint; 'soas' silences the
-- same warning in its generated module, as it does the orphan 'ZipMatchK'
-- instance for the raw identifier type.
{-# OPTIONS_GHC -Wno-missing-signatures -Wno-redundant-constraints -Wno-orphans #-}

-- | The scope-safe syntax generated from
-- "Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config".
--
-- That this module /compiles at all/ is the regression test: before the fix,
-- 'mkFreeFoil' and 'mkFreeFoilConversions' generated ill-typed code for @Let@
-- and @LetRec@ (a pattern synonym whose signature disagreed with its arguments,
-- and conversions that gave the raw constructor the wrong number of arguments in
-- the wrong order).
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Syntax where

import qualified Control.Monad.Foil                              as Foil
import           Control.Monad.Free.Foil.TH.MkFreeFoil
import           Data.Bifunctor.TH
import           Data.ZipMatchK
import           Generics.Kind.TH                                (deriveGenericK)

import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config

mkFreeFoil config

deriveGenericK ''FFPattern
instance Foil.SinkableK FFPattern
instance Foil.HasNameBinders FFPattern
instance Foil.CoSinkable FFPattern
instance Foil.UnifiablePattern FFPattern

deriveBifunctor ''TermSig
deriveBifoldable ''TermSig
deriveBitraversable ''TermSig

deriveGenericK ''TermSig
instance ZipMatchK VarIdent where zipMatchWithK = zipMatchViaEq
instance ZipMatchK TermSig

mkFreeFoilConversions config
