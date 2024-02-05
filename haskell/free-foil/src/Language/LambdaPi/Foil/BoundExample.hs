{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-} -- Убрать
{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Убрать
module Language.LambdaPi.Foil.BoundExample where

import Data.String (IsString, String)

import Language.LambdaPi.Foil (Scope(..), Name (UnsafeName), NameBinder(UnsafeNameBinder)
                            , extendScope, withFresh, sink, Distinct
                            , nameOf, ppName, Sinkable(..), extendRenaming)
import Language.LambdaPi.Foil.TH
import qualified Language.LambdaPi.Foil.TH as TH
import Language.LambdaPi.Bound.Abs
import qualified Language.Haskell.TH as Foil
import Unsafe.Coerce (unsafeCoerce)
import Language.Haskell.TH (nameBase)

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern


substitute :: FoilTerm o -> FoilTerm i -> FoilTerm o
substitute substTerm = \case
  FoilVar name -> substTerm
  FoilApp term1 term2 -> substTerm
  FoilLam (FoilPatternVar pat) (FoilAScopedTerm term) -> substituteHelper substTerm (nameOf pat) term
    where
      substituteHelper :: FoilTerm o -> Name i -> FoilTerm i -> FoilTerm o
      substituteHelper substTerm substName = \case
        FoilVar name 
          | ppName name == ppName substName -> substTerm
          | otherwise -> FoilVar (UnsafeName (ppName name))
        FoilApp term1 term2 -> FoilApp (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2) 
        FoilLam (FoilPatternVar pat) (FoilAScopedTerm term)
          | ppName (nameOf pat) == ppName substName -> substituteHelper substTerm (UnsafeName (ppName substName)) term
          | otherwise -> FoilLam (FoilPatternVar newPat) (FoilAScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
            where
              newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))

two :: Term
two = Lam (PatternVar "s") (AScopedTerm (Lam (PatternVar "z") (AScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

-- twoFoil :: FoilTerm n
-- twoFoil = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "s"))) (FoilAScopedTerm (FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "s")) (FoilApp (FoilVar (UnsafeName "s")) (FoilVar (UnsafeName "z")))))))

-- foilFour :: FoilTerm n
-- foilFour = FoilVar (UnsafeName "zz" :: Name n)

-- func :: VarIdent -> Name n 
-- func (VarIdent s) = UnsafeName s :: Name n

-- substed = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "zz")) (FoilApp (FoilVar (UnsafeName "zz")) (FoilVar (UnsafeName "z")))))

-- -- Language.LambdaPi.Foil.BoundExample.toFoilTerm Language.LambdaPi.Foil.BoundExample.func Language.LambdaPi.Foil.emptyScope Language.LambdaPi.Foil.BoundExample.two