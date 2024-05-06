{-# OPTIONS_GHC -ddump-splices #-}
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
-- {-# OPTIONS_GHC -Wno-name-shadowing #-} -- Убрать
-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Убрать
module Language.LambdaPi.Foil.LambdaPiExample where

import Language.LambdaPi.Foil (Scope(..), Name (UnsafeName), NameBinder(UnsafeNameBinder)
                            , Distinct
                            , nameOf, ppName, Sinkable(..), CoSinkable(..))
import Language.LambdaPi.Foil.TH
import Language.LambdaPi.LambdaPi.Abs
import Unsafe.Coerce (unsafeCoerce)
import Language.LambdaPi.Foil.NewExample (substTerm)

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern


substitute :: FoilTerm o -> FoilTerm i -> FoilTerm o
substitute substTerm = \case
  FoilVar {} -> substTerm
  FoilPair {} -> substTerm 
  FoilApp {} -> substTerm
  FoilPi {} -> substTerm
  FoilLam FoilPatternWildcard (FoilAScopedTerm term) ->  stopSubstitute term
  FoilLam (FoilPatternPair pat1 pat2) (FoilAScopedTerm term) -> substTerm
  FoilLam (FoilPatternVar pat) (FoilAScopedTerm term) -> substituteHelper substTerm (nameOf pat) term
    where
      substituteHelper :: FoilTerm o -> Name i -> FoilTerm i -> FoilTerm o
      substituteHelper substTerm substName = \case
        FoilVar name
          | ppName name == ppName substName -> substTerm
          | otherwise -> FoilVar (UnsafeName (ppName name))
        FoilPair term1 term2 -> FoilPair (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2) 
        FoilApp term1 term2 -> FoilApp (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2)
        FoilPi (FoilPatternVar pat) term (FoilAScopedTerm scopeTerm) 
          | ppName (nameOf pat) == ppName substName -> FoilPi (FoilPatternVar newPat) (substituteHelper substTerm (UnsafeName (ppName substName)) term) (FoilAScopedTerm (stopSubstitute scopeTerm))
          | otherwise -> FoilPi (FoilPatternVar newPat) (substituteHelper substTerm (UnsafeName (ppName substName)) term) (FoilAScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) scopeTerm))
            where
              newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))
        FoilPi FoilPatternWildcard term (FoilAScopedTerm scopeTerm) -> 
          FoilPi FoilPatternWildcard (substituteHelper substTerm substName term) (FoilAScopedTerm (substituteHelper substTerm substName scopeTerm))
        -- FoilPi (FoilPatternPair pat1 pat2) term (FoilAScopedTerm scopeTerm) -> _
        FoilLam FoilPatternWildcard (FoilAScopedTerm term) ->  
          FoilLam FoilPatternWildcard (FoilAScopedTerm (substituteHelper substTerm substName scopeTerm))
        -- FoilLam (FoilPatternPair pat1 pat2) (FoilAScopedTerm term) -> _
        FoilLam (FoilPatternVar pat) (FoilAScopedTerm term)
          | ppName (nameOf pat) == ppName substName -> FoilLam (FoilPatternVar newPat) (FoilAScopedTerm (stopSubstitute term)) -- substituteHelper substTerm (UnsafeName (ppName substName)) term
          | otherwise -> FoilLam (FoilPatternVar newPat) (FoilAScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
            where
              newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))

stopSubstitute :: FoilTerm i -> FoilTerm o
stopSubstitute = \case 
  FoilVar name -> FoilVar (UnsafeName (ppName name))
  FoilPair term1 term2 -> FoilPair (stopSubstitute term1) (stopSubstitute term2)
  FoilApp term1 term2 -> FoilApp (stopSubstitute term1) (stopSubstitute term2)
  FoilPi FoilPatternWildcard term1 (FoilAScopedTerm term) -> FoilPi FoilPatternWildcard (stopSubstitute term1) (FoilAScopedTerm (stopSubstitute term))
  FoilPi (FoilPatternVar pat) term1 (FoilAScopedTerm term) -> FoilPi (FoilPatternVar newPat) (stopSubstitute term1) (FoilAScopedTerm (stopSubstitute term))
    where
      newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))
  FoilPi (FoilPatternPair pat1 pat2) term1 (FoilAScopedTerm term) -> FoilPi (FoilPatternPair newPat1 newPat2) (stopSubstitute term1) (FoilAScopedTerm (stopSubstitute term))
    where
      newPat1 = UnsafeNameBinder (UnsafeName (ppName (nameOf pat1)))
      newPat2 = UnsafeNameBinder (UnsafeName (ppName (nameOf pat2)))
  
  FoilLam (FoilPatternVar pat) (FoilAScopedTerm term) -> FoilLam (FoilPatternVar newPat) (FoilAScopedTerm (stopSubstitute term)) 
    where
      newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))
  FoilLam (FoilPatternPair pat1 pat2) (FoilAScopedTerm term) -> FoilLam (FoilPatternPair newPat1 newPat2) (FoilAScopedTerm (stopSubstitute term)) 
    where
      newPat1 = UnsafeNameBinder (UnsafeName (ppName (nameOf pat1)))
      newPat2 = UnsafeNameBinder (UnsafeName (ppName (nameOf pat2)))
  FoilLam FoilPatternWildcard (FoilAScopedTerm term) -> FoilLam FoilPatternWildcard (FoilAScopedTerm (stopSubstitute term)) 

foilLam :: FoilTerm n
foilLam = FoilLam 
            (FoilPatternVar (UnsafeNameBinder (UnsafeName "s"))) 
            (FoilAScopedTerm (FoilLam 
                                (FoilPatternVar (UnsafeNameBinder (UnsafeName "s"))) 
                                (FoilAScopedTerm (FoilApp 
                                                    (FoilVar (UnsafeName "s")) 
                                                    (FoilApp 
                                                      (FoilVar (UnsafeName "s")) 
                                                      (FoilVar (UnsafeName "s")))))))

foilTerm :: FoilTerm n
foilTerm = FoilVar (UnsafeName "aa" :: Name n)

-- two :: Term
-- two = Lam (PatternVar "s") (AScopedTerm (Lam (PatternVar "z") (AScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

-- func :: VarIdent -> Name n
-- func (VarIdent s) = UnsafeName s :: Name n

-- substed = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "zz")) (FoilApp (FoilVar (UnsafeName "zz")) (FoilVar (UnsafeName "z")))))

-- -- Language.LambdaPi.Foil.LambdaPiExample.toFoilTerm Language.LambdaPi.Foil.LambdaPiExample.func Language.LambdaPi.Foil.emptyScope Language.LambdaPi.Foil.LambdaPiExample.two
