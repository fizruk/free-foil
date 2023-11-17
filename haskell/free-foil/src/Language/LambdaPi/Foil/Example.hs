{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
module Language.LambdaPi.Foil.Example where

import Language.LambdaPi.Foil
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
  deriving (Show)

data ScopedTerm = ScopedTerm Term
  deriving (Show)

mkFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
