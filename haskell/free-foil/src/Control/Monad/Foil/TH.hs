{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Control.Monad.Foil.TH (
  module Control.Monad.Foil.TH.MkFoilData,
  module Control.Monad.Foil.TH.MkToFoil,
  module Control.Monad.Foil.TH.MkFromFoil,
  module Control.Monad.Foil.TH.MkInstancesFoil
) where

import           Control.Monad.Foil.TH.MkFoilData
import           Control.Monad.Foil.TH.MkFromFoil
import           Control.Monad.Foil.TH.MkInstancesFoil
import           Control.Monad.Foil.TH.MkToFoil

-- Foil

-- data FoilTerm n where
--   FoilVar :: Foil.Name n -> FoilTerm n
--   FoilApp :: FoilTerm n -> FoilTerm n -> FoilTerm n
--   FoilLam :: FoilPattern n l -> FoilTerm l -> FoilTerm n

-- data FoilPattern n l where
--   FoilPatternVar :: Foil.NameBinder n l -> FoilPattern n l

-- data FoilScopedTerm n where
--   FoilScopedTerm :: FoilTerm n -> FoilScopedTerm n
