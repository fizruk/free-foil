{-# LANGUAGE TemplateHaskell #-}

-- | A raw syntax in the shape BNFC produces, used to test 'mkFreeFoil'.
--
-- The interesting constructors are the ones whose /raw/ shape does not line up
-- with the free foil node they become:
--
-- * @Let@ has a pattern, a term, and one scoped term (so the pattern is not
--   adjacent to the scope it binds);
-- * @LetRec@ has a pattern and __two__ scoped terms (so one raw binder binds
--   two separate scopes).
--
-- Both used to generate ill-typed code. See the spec.
--
-- The config lives in its own module because Template Haskell may not splice a
-- value defined in the same module.
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config where

import           Control.Monad.Free.Foil.TH.MkFreeFoil

newtype VarIdent = VarIdent String
  deriving (Eq, Ord, Show)

newtype Pattern = PatternVar VarIdent
  deriving (Eq, Show)

newtype ScopedTerm = ScopedTerm Term
  deriving (Eq, Show)

data Term
  = Var VarIdent
  | App Term Term
  | Fun Pattern ScopedTerm                -- ^ pattern, then its scope (this always worked)
  | Let Pattern Term ScopedTerm           -- ^ a term between the pattern and its scope
  | LetRec Pattern ScopedTerm ScopedTerm  -- ^ one pattern binding two scopes
  deriving (Eq, Show)

rawVar :: VarIdent -> Term
rawVar = Var

intToVarIdent :: Int -> VarIdent
intToVarIdent i = VarIdent ("x" <> show i)

rawScopedTerm :: Term -> ScopedTerm
rawScopedTerm = ScopedTerm

rawScopeToTerm :: ScopedTerm -> Term
rawScopeToTerm (ScopedTerm t) = t

config :: FreeFoilConfig
config = FreeFoilConfig
  { rawQuantifiedNames = []
  , freeFoilTermConfigs =
      [ FreeFoilTermConfig
          { rawIdentName = ''VarIdent
          , rawTermName = ''Term
          , rawBindingName = ''Pattern
          , rawScopeName = ''ScopedTerm
          , rawVarConName = 'Var
          , rawSubTermNames = []
          , rawSubScopeNames = []
          , intToRawIdentName = 'intToVarIdent
          , rawVarIdentToTermName = 'rawVar
          , rawTermToScopeName = 'rawScopedTerm
          , rawScopeToTermName = 'rawScopeToTerm
          } ]
  , freeFoilNameModifier = ("FF" ++)
  , freeFoilScopeNameModifier = ("FFScoped" ++)
  , freeFoilConNameModifier = ("FF" ++)
  , freeFoilConvertFromName = ("from" ++)
  , freeFoilConvertToName = ("to" ++)
  , signatureNameModifier = (++ "Sig")
  }
