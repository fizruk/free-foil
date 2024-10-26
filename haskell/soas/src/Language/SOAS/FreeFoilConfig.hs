{-# LANGUAGE TemplateHaskell #-}
module Language.SOAS.FreeFoilConfig where

import qualified Language.SOAS.Syntax.Abs    as Raw
import           Control.Monad.Free.Foil.TH.MkFreeFoil

intToVarIdent :: Int -> Raw.VarIdent
intToVarIdent i = Raw.VarIdent ("x" <> show i)

intToTypeVarIdent :: Int -> Raw.TypeVarIdent' a
intToTypeVarIdent = Raw.TypeVarIdent (error "trying to access an erased annotation") . intToVarIdent

rawVar :: Raw.VarIdent -> Raw.Term' a
rawVar = Raw.Var (error "trying to access an erased annotation")

rawTypeVar :: Raw.TypeVarIdent' a -> Raw.Type' a
rawTypeVar = Raw.TypeVar (error "trying to access an erased annotation")

rawScopedTerm :: Raw.Term' a -> Raw.ScopedTerm' a
rawScopedTerm = Raw.ScopedTerm (error "trying to access an erased annotation")

rawScopedType :: Raw.Type' a -> Raw.ScopedType' a
rawScopedType = Raw.ScopedType (error "trying to access an erased annotation")

soasConfig :: FreeFoilConfig
soasConfig = FreeFoilConfig
  { rawQuantifiedNames =
      [ ''Raw.Subst'
      , ''Raw.MetaVarTyping'
      , ''Raw.OpTyping'
      , ''Raw.Constraint'
      , ''Raw.VarTyping'
      , ''Raw.TermTyping'
      ]
  , freeFoilTermConfigs =
      [ FreeFoilTermConfig
          { rawIdentName = ''Raw.VarIdent
          , rawTermName = ''Raw.Term'
          , rawBindingName = ''Raw.Binders'
          , rawScopeName = ''Raw.ScopedTerm'
          , rawVarConName = 'Raw.Var
          , rawSubTermNames = [ ''Raw.OpArg' ]
          , intToRawIdentName = 'intToVarIdent
          , rawVarIdentToTermName = 'rawVar
          , rawTermToScopeName = 'rawScopedTerm
          }
      , FreeFoilTermConfig
          { rawIdentName = ''Raw.TypeVarIdent'
          , rawTermName = ''Raw.Type'
          , rawBindingName = ''Raw.TypeBinders'
          , rawScopeName = ''Raw.ScopedType'
          , rawVarConName = 'Raw.TypeVar
          , rawSubTermNames = [ ''Raw.OpArgTyping' ]
          , intToRawIdentName = 'intToTypeVarIdent
          , rawVarIdentToTermName = 'rawTypeVar
          , rawTermToScopeName = 'rawScopedType
          } ]
  , freeFoilNameModifier = id
  , freeFoilScopeNameModifier = ("Scoped" ++ )
  , freeFoilConNameModifier = id
  , freeFoilConvertFromName = ("from" ++ )
  , freeFoilConvertToName = ("to" ++ )
  , signatureNameModifier = (++ "Sig")
  , ignoreNames = []
  }