{-# LANGUAGE TemplateHaskell #-}
-- | The 'FreeFoilConfig' driving the Template Haskell generation for MLTT.
--
-- There is a single term sort, so a single 'FreeFoilTermConfig'. Patterns are
-- a proper syntactic category ('Raw.Pattern'', with wildcards, variables and
-- pairs), which is what makes this demo exercise free foil's /custom pattern/
-- layer rather than a flat list of binders.
module Language.MLTT.FreeFoilConfig where

import           Control.Monad.Free.Foil.TH.MkFreeFoil
import qualified Language.MLTT.Syntax.Abs              as Raw

-- | Name a bound variable after its underlying integer identifier.
intToVarIdent :: Int -> Raw.VarIdent
intToVarIdent i = Raw.VarIdent ("x" <> show i)

-- | The variable constructor, with the annotation erased.
rawVar :: Raw.VarIdent -> Raw.Term' a
rawVar = Raw.Var (error "trying to access an erased annotation")

-- | Wrap a raw term into a raw scoped term, with the annotation erased.
rawScopedTerm :: Raw.Term' a -> Raw.ScopedTerm' a
rawScopedTerm = Raw.AScopedTerm (error "trying to access an erased annotation")

-- | Extract a raw term from a raw scoped term.
rawScopeToTerm :: Raw.ScopedTerm' a -> Raw.Term' a
rawScopeToTerm (Raw.AScopedTerm _loc term) = term

-- | The configuration used by "Language.MLTT.Impl.Generated".
mlttConfig :: FreeFoilConfig
mlttConfig = FreeFoilConfig
  { rawQuantifiedNames = []
  , freeFoilTermConfigs =
      [ FreeFoilTermConfig
          { rawIdentName = ''Raw.VarIdent
          , rawTermName = ''Raw.Term'
          , rawBindingName = ''Raw.Pattern'
          , rawScopeName = ''Raw.ScopedTerm'
          , rawVarConName = 'Raw.Var
          , rawSubTermNames = []
          , rawSubScopeNames = []
          , intToRawIdentName = 'intToVarIdent
          , rawVarIdentToTermName = 'rawVar
          , rawTermToScopeName = 'rawScopedTerm
          , rawScopeToTermName = 'rawScopeToTerm
          } ]
  , freeFoilNameModifier = id
  , freeFoilScopeNameModifier = ("Scoped" ++)
  , freeFoilConNameModifier = id
  , freeFoilConvertFromName = ("from" ++)
  , freeFoilConvertToName = ("to" ++)
  , signatureNameModifier = (++ "Sig")
  }
