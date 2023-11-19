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
module Language.LambdaPi.Foil.Example where

import Data.String (IsString)

import Language.LambdaPi.Foil (Scope(UnsafeScope), Name, NameBinder(UnsafeNameBinder)
                            , extendScope, withFresh, sink, Distinct
                            , nameOf, ppName, Sinkable(..), extendRenaming)
import Language.LambdaPi.Foil.TH
import Unsafe.Coerce

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

two :: Term
two = Lam (PatternVar "s") (ScopedTerm (Lam (PatternVar "z") (ScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

mkFoil ''Term ''VarIdent ''ScopedTerm ''Pattern

toFoilTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> Term -> FoilTerm n
toFoilTerm toName scope = \case
    Var x -> FoilVar (toName x)
    Lit n -> FoilLit n
    App fun arg -> FoilApp (toFoilTerm toName scope fun) (toFoilTerm toName scope arg)
    Lam pat scopedTerm -> withPattern toName scope pat $ \pat' toName' scope' ->
      FoilLam pat' (toFoilScopedTerm toName' scope' scopedTerm)

withPattern
  :: Distinct n
  => (VarIdent -> Name n)
  -> Scope n
  -> Pattern
  -> (forall l. Distinct l => FoilPattern n l -> (VarIdent -> Name l) -> Scope l -> r)
  -> r
withPattern toName scope pat cont =
  case pat of
    PatternVar var -> withFresh scope $ \binder ->
      let scope' = extendScope binder scope
          toName' x
            | x == var = nameOf binder
            | otherwise = sink (toName x)
          pat' = toFoilPattern binder pat
      in cont pat' toName' scope'

    PatternLit n ->
      let pat' = FoilPatternLit n
      in cont pat' toName scope

toFoilPattern :: NameBinder n l -> Pattern -> FoilPattern n l
toFoilPattern binder = \case
  PatternVar _ -> FoilPatternVar binder
  PatternLit n -> FoilPatternLit n

toFoilScopedTerm :: Distinct n => (VarIdent -> Name n) -> Scope n -> ScopedTerm -> FoilScopedTerm n
toFoilScopedTerm toName scope = \case
  ScopedTerm term -> FoilScopedTerm (toFoilTerm toName scope term)


fromFoilTerm :: (Name n -> VarIdent) -> Scope n -> FoilTerm n -> Term 
fromFoilTerm fromName scope = \case
    FoilVar x -> Var (fromName x) 
    FoilLit n -> Lit n
    FoilApp fun arg -> App (fromFoilTerm fromName scope fun) (fromFoilTerm fromName scope arg)
    FoilLam pat scopedTerm -> withoutPattern fromName scope pat $ \pat' toName' scope' ->
      Lam pat' (fromFoilScopedTerm toName' scope' scopedTerm)

withoutPattern
  :: (Name n -> VarIdent)
  -> Scope n
  -> FoilPattern n l
  -> (Pattern -> (Name l -> VarIdent) -> Scope l -> r)
  -> r
withoutPattern fromName scope pat cont =
  case pat of
    FoilPatternVar binder ->
      let scope' = extendScope binder scope
          fromName' x  
            | ppName x == ppName (nameOf binder) = VarIdent (ppName (nameOf binder)) -- Точно через ppName ???
            | otherwise = VarIdent (ppName x)
      in let pat' = PatternVar (fromName' (nameOf binder))
      in cont pat' fromName' scope'

    FoilPatternLit n -> 
      let pat' = PatternLit n
          fromName' x = VarIdent (ppName x) -- Sham scope expansion
          scope' = unsafeCoerce scope
      in cont pat' fromName' scope'

fromFoilScopedTerm :: (Name n -> VarIdent) -> Scope n -> FoilScopedTerm n -> ScopedTerm
fromFoilScopedTerm fromName scope = \case
  FoilScopedTerm term -> ScopedTerm (fromFoilTerm fromName scope term)

instance Sinkable FoilTerm where
  sinkabilityProof f (FoilVar n) = FoilVar (f n)
  sinkabilityProof _ (FoilLit i) = FoilLit i
  sinkabilityProof f (FoilApp t1 t2) = FoilApp (sinkabilityProof f t1) (sinkabilityProof f t2)
  sinkabilityProof f (FoilLam (FoilPatternVar binder) (FoilScopedTerm body)) = extendRenaming f binder (\f' binder' ->
      FoilLam (FoilPatternVar binder') (FoilScopedTerm (sinkabilityProof f' body)))

instance Sinkable (FoilPattern n) where
  sinkabilityProof f (FoilPatternVar (UnsafeNameBinder var)) = FoilPatternVar (UnsafeNameBinder (f var))
  sinkabilityProof _ (FoilPatternLit i) = FoilPatternLit i

instance Sinkable FoilScopedTerm where
  sinkabilityProof f (FoilScopedTerm t) = FoilScopedTerm (sinkabilityProof f t)