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
module Language.LambdaPi.Foil.Example where

import Data.String (IsString)

import Language.LambdaPi.Foil (Scope(..), Name (UnsafeName), NameBinder(UnsafeNameBinder)
                            , extendScope, withFresh, sink, Distinct
                            , nameOf, ppName, Sinkable(..), extendRenaming)
import Language.LambdaPi.Foil.TH
import qualified Language.LambdaPi.Foil.TH as TH
import qualified Language.Haskell.TH as Foil

data Term
  = Var VarIdent
  | Lit !Int
  | App Term Term
  | Lam Pattern ScopedTerm
  deriving (Show)

data Pattern
  = PatternVar VarIdent
  | PatternLit !Int
  deriving (Show)

newtype VarIdent = VarIdent String
  deriving newtype (Show, Eq, IsString)

data ScopedTerm = ScopedTerm Term
  deriving (Show)

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern

-- toFoilTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> Term -> FoilTerm n
-- toFoilTerm toName scope = \case
--     Var x -> FoilVar (toName x)
--     Lit n -> FoilLit n
--     App fun arg -> FoilApp (toFoilTerm toName scope fun) (toFoilTerm toName scope arg)
--     Lam pat scopedTerm -> withPattern toName scope pat $ \pat' toName' scope' ->
--       FoilLam pat' (toFoilScopedTerm toName' scope' scopedTerm) 


-- withPattern
--   :: Distinct n
--   => (VarIdent -> Name n)
--   -> Scope n
--   -> Pattern
--   -> (forall l. Distinct l => FoilPattern n l -> (VarIdent -> Name l) -> Scope l -> r)
--   -> r
-- withPattern toName scope pat cont =
--   case pat of
--     PatternVar var -> withFresh scope $ \binder ->
--       let scope' = extendScope binder scope
--           toName' x
--             | x == var = nameOf binder
--             | otherwise = sink (toName x)
--           pat' = toFoilPattern binder pat
--       in cont pat' toName' scope'

--     PatternLit n ->
--       let pat' = FoilPatternLit n
--       in cont pat' toName scope

-- toFoilPattern :: NameBinder n l -> Pattern -> FoilPattern n l
-- toFoilPattern binder = \case
--   PatternVar _ -> FoilPatternVar binder
--   PatternLit n -> FoilPatternLit n

-- toFoilScopedTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> ScopedTerm -> FoilScopedTerm n
-- toFoilScopedTerm toName scope = \case
--   ScopedTerm term -> FoilScopedTerm (toFoilTerm toName scope term)


-- fromFoilTerm :: FoilTerm n -> Term 
-- fromFoilTerm = \case
--   FoilVar x -> Var (VarIdent (ppName x)) 
--   FoilLit n -> Lit n
--   FoilApp fun arg -> App (fromFoilTerm fun) (fromFoilTerm arg)
--   FoilLam pat scopedTerm -> Lam (fromFoilPattern pat) (fromFoilScopedTerm scopedTerm)

-- fromFoilPattern :: FoilPattern n l -> Pattern
-- fromFoilPattern = \case
--     FoilPatternVar (UnsafeNameBinder binder) -> PatternVar (VarIdent (ppName binder))
--     FoilPatternLit n -> PatternLit n

-- fromFoilScopedTerm :: FoilScopedTerm n -> ScopedTerm
-- fromFoilScopedTerm = \case
--   FoilScopedTerm term -> ScopedTerm (fromFoilTerm term)

instance Sinkable FoilTerm where
  sinkabilityProof :: (Name n -> Name l) -> FoilTerm n -> FoilTerm l
  sinkabilityProof f (FoilVar n) = FoilVar (f n)
  sinkabilityProof _ (FoilLit i) = FoilLit i
  sinkabilityProof f (FoilApp t1 t2) = FoilApp (sinkabilityProof f t1) (sinkabilityProof f t2)
  sinkabilityProof f (FoilLam binder (FoilScopedTerm body)) = case binder of 
    FoilPatternLit binder -> FoilLam (FoilPatternLit binder) (FoilScopedTerm body)
    FoilPatternVar binder -> extendRenaming f binder (\f' binder' ->
      FoilLam (FoilPatternVar binder') (FoilScopedTerm (sinkabilityProof f' body)))

-- instance Sinkable (FoilPattern n) where
--   sinkabilityProof :: (Name n2 -> Name l) -> FoilPattern n1 n2 -> FoilPattern n1 l
--   sinkabilityProof f (FoilPatternVar (UnsafeNameBinder var)) = FoilPatternVar (UnsafeNameBinder (f var))
--   sinkabilityProof _ (FoilPatternLit i) = FoilPatternLit i

-- instance Sinkable FoilScopedTerm where
--   sinkabilityProof :: (Name n -> Name l) -> FoilScopedTerm n -> FoilScopedTerm l
--   sinkabilityProof f (FoilScopedTerm t) = FoilScopedTerm (sinkabilityProof f t)


substitute :: FoilTerm o -> FoilTerm i -> FoilTerm o
substitute substTerm = \case
  FoilVar name -> substTerm
  FoilLit n -> substTerm
  FoilApp term1 term2 -> substTerm
  FoilLam (FoilPatternLit pat) (FoilScopedTerm term) -> FoilLam (FoilPatternLit pat) (FoilScopedTerm term)
  FoilLam (FoilPatternVar pat) (FoilScopedTerm term) -> substituteHelper substTerm (nameOf pat) term
    where
      substituteHelper :: FoilTerm o -> Name i -> FoilTerm i -> FoilTerm o
      substituteHelper substTerm substName = \case
        FoilVar name 
          | ppName name == ppName substName -> substTerm
          | otherwise -> FoilVar (UnsafeName (ppName name))
        FoilLit n -> FoilLit n
        FoilApp term1 term2 -> FoilApp (substituteHelper substTerm substName term1) (substituteHelper substTerm substName term2) 
        FoilLam (FoilPatternLit pat) (FoilScopedTerm term) -> FoilLam (FoilPatternLit pat) (FoilScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
        FoilLam (FoilPatternVar pat) (FoilScopedTerm term)
          | ppName (nameOf pat) == ppName substName -> substituteHelper substTerm (UnsafeName (ppName substName)) term
          | otherwise -> FoilLam (FoilPatternVar newPat) (FoilScopedTerm (substituteHelper substTerm (UnsafeName (ppName substName)) term))
            where
              newPat = UnsafeNameBinder (UnsafeName (ppName (nameOf pat)))


two :: Term
two = Lam (PatternVar "s") (ScopedTerm (Lam (PatternVar "z") (ScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

foilTwo :: FoilTerm n
foilTwo = FoilLam 
            (FoilPatternVar (UnsafeNameBinder (UnsafeName "s"))) 
            (FoilScopedTerm (FoilLam 
                              (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) 
                              (FoilScopedTerm (FoilApp 
                                                  (FoilVar (UnsafeName "s")) 
                                                  (FoilApp 
                                                      (FoilVar (UnsafeName "s")) 
                                                      (FoilVar (UnsafeName "z")))))))

foilThree :: Name n
foilThree = UnsafeName "s" :: Name n

foilFour :: FoilTerm n
foilFour = FoilVar (UnsafeName "zz" :: Name n)

func :: VarIdent -> Name n 
func (VarIdent s) = UnsafeName s :: Name n