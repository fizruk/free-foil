{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.LambdaPi.Foil.Example where

import Data.String (IsString)

import Language.LambdaPi.Foil (Scope, Name, NameBinder, extendScope, withFresh, sink, Distinct, nameOf)
import Language.LambdaPi.Foil.TH

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
