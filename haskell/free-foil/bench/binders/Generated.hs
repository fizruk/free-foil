{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | The syntax that 'mkFreeFoil' generates from "Config", whose pattern type
-- 'FFBPattern' has the 'Control.Monad.Foil.CoSinkable' instance it generates.
module Generated where

import           Control.Monad.Free.Foil.TH.MkFreeFoil (mkFreeFoil)
import           Data.Bifunctor.TH                     (deriveBifunctor)

import           Config

mkFreeFoil bConfig

deriveBifunctor ''BTermSig
