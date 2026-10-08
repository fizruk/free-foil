{-# LANGUAGE TemplateHaskell #-}

-- | A raw syntax for 'mkFreeFoil' whose patterns are variables and pairs, in
-- its own module because Template Haskell may not splice a value defined in
-- the same module. It follows @PatternsConfig@ of the test suite.
module Config where

import           Control.Monad.Free.Foil.TH.MkFreeFoil

newtype BVarIdent = BVarIdent String

data BPattern
  = BPatternVar BVarIdent
  | BPatternPair BPattern BPattern

newtype BScopedTerm = BScopedTerm BTerm

data BTerm
  = BVar BVarIdent
  | BFun BPattern BScopedTerm

intToBVarIdent :: Int -> BVarIdent
intToBVarIdent i = BVarIdent ("x" <> show i)

bVar :: BVarIdent -> BTerm
bVar = BVar

bTermToScope :: BTerm -> BScopedTerm
bTermToScope = BScopedTerm

bScopeToTerm :: BScopedTerm -> BTerm
bScopeToTerm (BScopedTerm t) = t

bConfig :: FreeFoilConfig
bConfig = FreeFoilConfig
  { rawQuantifiedNames = []
  , freeFoilTermConfigs =
      [ FreeFoilTermConfig
          { rawIdentName = ''BVarIdent
          , rawTermName = ''BTerm
          , rawBindingName = ''BPattern
          , rawScopeName = ''BScopedTerm
          , rawVarConName = 'BVar
          , rawSubTermNames = []
          , rawSubScopeNames = []
          , intToRawIdentName = 'intToBVarIdent
          , rawVarIdentToTermName = 'bVar
          , rawTermToScopeName = 'bTermToScope
          , rawScopeToTermName = 'bScopeToTerm
          } ]
  , freeFoilNameModifier = ("FF" ++)
  , freeFoilScopeNameModifier = ("FFScoped" ++)
  , freeFoilConNameModifier = ("FF" ++)
  , freeFoilConvertFromName = ("from" ++)
  , freeFoilConvertToName = ("to" ++)
  , signatureNameModifier = (++ "Sig")
  }
