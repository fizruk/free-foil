{-# LANGUAGE TemplateHaskell #-}
module Language.SOAS.FreeFoilConfig where

import qualified Language.SOAS.Syntax.Abs    as Raw
import           Control.Monad.Free.Foil.TH.MkFreeFoil

intToVarIdent :: Int -> Raw.VarIdent
intToVarIdent i = Raw.VarIdent ("x" <> show i)

rawVar :: Raw.VarIdent -> Raw.Term' a
rawVar = Raw.Var (error "trying to access an erased annotation")

rawTypeVar :: Raw.VarIdent -> Raw.Type' a
rawTypeVar = Raw.TypeVar (error "trying to access an erased annotation")

rawScopedTerm :: Raw.Term' a -> Raw.ScopedTerm' a
rawScopedTerm = Raw.ScopedTerm (error "trying to access an erased annotation")

rawScopedType :: Raw.Type' a -> Raw.ScopedType' a
rawScopedType = Raw.ScopedType (error "trying to access an erased annotation")

rawScopeToTerm :: Raw.ScopedTerm' a -> Raw.Term' a
rawScopeToTerm (Raw.ScopedTerm _loc term) = term

rawScopeToType :: Raw.ScopedType' a -> Raw.Type' a
rawScopeToType (Raw.ScopedType _loc type_) = type_

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
          , rawSubScopeNames = []
          , intToRawIdentName = 'intToVarIdent
          , rawVarIdentToTermName = 'rawVar
          , rawTermToScopeName = 'rawScopedTerm
          , rawScopeToTermName = 'rawScopeToTerm
          }
      , FreeFoilTermConfig
          { rawIdentName = ''Raw.VarIdent
          , rawTermName = ''Raw.Type'
          , rawBindingName = ''Raw.TypeBinders'
          , rawScopeName = ''Raw.ScopedType'
          , rawVarConName = 'Raw.TypeVar
          , rawSubTermNames = [ ''Raw.OpArgTyping' ]
          , rawSubScopeNames = [ ''Raw.ScopedOpArgTyping' ]
          , intToRawIdentName = 'intToVarIdent
          , rawVarIdentToTermName = 'rawTypeVar
          , rawTermToScopeName = 'rawScopedType
          , rawScopeToTermName = 'rawScopeToType
          } ]
  , freeFoilNameModifier = id
  , freeFoilScopeNameModifier = ("Scoped" ++ )
  , freeFoilConNameModifier = id
  , freeFoilConvertFromName = ("from" ++ )
  , freeFoilConvertToName = ("to" ++ )
  , signatureNameModifier = (++ "Sig")
  }
