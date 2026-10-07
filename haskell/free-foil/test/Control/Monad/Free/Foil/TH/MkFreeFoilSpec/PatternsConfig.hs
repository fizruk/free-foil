{-# LANGUAGE TemplateHaskell #-}

-- | Raw syntaxes whose pattern types are not a single binder, used to test the
-- pattern types that 'mkFreeFoil' generates (see
-- "Control.Monad.Free.Foil.TH.PatternTypesSpec"):
--
-- * @MPattern@ has several constructors (a wildcard, a variable and a pair),
--   so its scope-safe version is @data@;
-- * @APattern@ has one constructor with two fields (an annotation and a
--   variable, the shape BNFC produces), so its scope-safe version is @data@ too;
-- * @NPattern@ has one constructor whose one field is a nested pattern, so its
--   scope-safe version is a @newtype@.
--
-- The single-binder case is "Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config".
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsConfig where

import           Control.Monad.Free.Foil.TH.MkFreeFoil
import           Language.Haskell.TH                   (Name)

newtype MVarIdent = MVarIdent String
  deriving (Eq, Ord, Show)

data MPattern
  = MPatternWild
  | MPatternVar MVarIdent
  | MPatternPair MPattern MPattern
  deriving (Eq, Show)

newtype MScopedTerm = MScopedTerm MTerm
  deriving (Eq, Show)

data MTerm
  = MVar MVarIdent
  | MApp MTerm MTerm
  | MFun MPattern MScopedTerm
  deriving (Eq, Show)

newtype AVarIdent = AVarIdent String
  deriving (Eq, Ord, Show)

data APattern = APatternVar Int AVarIdent
  deriving (Eq, Show)

newtype AScopedTerm = AScopedTerm ATerm
  deriving (Eq, Show)

data ATerm
  = AVar AVarIdent
  | AFun APattern AScopedTerm
  deriving (Eq, Show)

newtype NVarIdent = NVarIdent String
  deriving (Eq, Ord, Show)

newtype NPattern = NPatternWrap MPattern
  deriving (Eq, Show)

newtype NScopedTerm = NScopedTerm NTerm
  deriving (Eq, Show)

data NTerm
  = NVar NVarIdent
  | NFun NPattern NScopedTerm
  deriving (Eq, Show)

intToMVarIdent :: Int -> MVarIdent
intToMVarIdent i = MVarIdent ("x" <> show i)

intToAVarIdent :: Int -> AVarIdent
intToAVarIdent i = AVarIdent ("x" <> show i)

intToNVarIdent :: Int -> NVarIdent
intToNVarIdent i = NVarIdent ("x" <> show i)

-- The conversions call these by name, so they are functions rather than
-- constructors.
mVar :: MVarIdent -> MTerm
mVar = MVar

aVar :: AVarIdent -> ATerm
aVar = AVar

nVar :: NVarIdent -> NTerm
nVar = NVar

mTermToScope :: MTerm -> MScopedTerm
mTermToScope = MScopedTerm

aTermToScope :: ATerm -> AScopedTerm
aTermToScope = AScopedTerm

nTermToScope :: NTerm -> NScopedTerm
nTermToScope = NScopedTerm

mScopeToTerm :: MScopedTerm -> MTerm
mScopeToTerm (MScopedTerm t) = t

aScopeToTerm :: AScopedTerm -> ATerm
aScopeToTerm (AScopedTerm t) = t

nScopeToTerm :: NScopedTerm -> NTerm
nScopeToTerm (NScopedTerm t) = t

termConfig :: Name -> Name -> Name -> Name -> Name -> Name -> Name -> Name -> Name -> FreeFoilTermConfig
termConfig ident term binding scope varCon var intToIdent termToScope scopeToTerm = FreeFoilTermConfig
  { rawIdentName = ident
  , rawTermName = term
  , rawBindingName = binding
  , rawScopeName = scope
  , rawVarConName = varCon
  , rawSubTermNames = []
  , rawSubScopeNames = []
  , intToRawIdentName = intToIdent
  , rawVarIdentToTermName = var
  , rawTermToScopeName = termToScope
  , rawScopeToTermName = scopeToTerm
  }

-- | The config for the conversions: all languages but the one of @NPattern@,
-- since the conversions do not support a pattern that nests the pattern of
-- another language.
conversionsConfig :: FreeFoilConfig
conversionsConfig = patternsConfig { freeFoilTermConfigs = take 2 (freeFoilTermConfigs patternsConfig) }

patternsConfig :: FreeFoilConfig
patternsConfig = FreeFoilConfig
  { rawQuantifiedNames = []
  , freeFoilTermConfigs =
      [ termConfig ''MVarIdent ''MTerm ''MPattern ''MScopedTerm 'MVar 'mVar 'intToMVarIdent 'mTermToScope 'mScopeToTerm
      , termConfig ''AVarIdent ''ATerm ''APattern ''AScopedTerm 'AVar 'aVar 'intToAVarIdent 'aTermToScope 'aScopeToTerm
      , termConfig ''NVarIdent ''NTerm ''NPattern ''NScopedTerm 'NVar 'nVar 'intToNVarIdent 'nTermToScope 'nScopeToTerm
      ]
  , freeFoilNameModifier = ("FF" ++)
  , freeFoilScopeNameModifier = ("FFScoped" ++)
  , freeFoilConNameModifier = ("FF" ++)
  , freeFoilConvertFromName = ("from" ++)
  , freeFoilConvertToName = ("to" ++)
  , signatureNameModifier = (++ "Sig")
  }
