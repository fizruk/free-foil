{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH (
  module Language.LambdaPi.Foil.TH.MkFoilData,
  module Language.LambdaPi.Foil.TH.MkToFoil,
  module Language.LambdaPi.Foil.TH.MkFromFoil,
  module Language.LambdaPi.Foil.TH.MkInstancesFoil
) where

import Language.LambdaPi.Foil.TH.MkFoilData
import Language.LambdaPi.Foil.TH.MkFromFoil
import Language.LambdaPi.Foil.TH.MkToFoil
import Language.LambdaPi.Foil.TH.MkInstancesFoil

-- Foil

-- data FoilTerm n where
--   FoilVar :: Foil.Name n -> FoilTerm n
--   FoilApp :: FoilTerm n -> FoilTerm n -> FoilTerm n
--   FoilLam :: FoilPattern n l -> FoilTerm l -> FoilTerm n

-- data FoilPattern n l where
--   FoilPatternVar :: Foil.NameBinder n l -> FoilPattern n l

-- data FoilScopedTerm n where
--   FoilScopedTerm :: FoilTerm n -> FoilScopedTerm n
