{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Language.SOAS.Impl where

import Data.List (find)
import Data.Bifunctor
import Data.Bifunctor.TH
import qualified Control.Monad.Foil as Foil
import           Control.Monad.Free.Foil.TH.MkFreeFoil
import           Control.Monad.Free.Foil
import qualified Language.SOAS.Syntax.Abs    as Raw
import qualified Language.SOAS.Syntax.Lex    as Raw
import qualified Language.SOAS.Syntax.Par    as Raw
import qualified Language.SOAS.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)
import Control.Monad.Free.Foil.Generic
import Generics.Kind.TH (deriveGenericK)
import qualified GHC.Generics as GHC

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

mkFreeFoil FreeFoilConfig
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
          }
      , FreeFoilTermConfig
          { rawIdentName = ''Raw.TypeVarIdent'
          , rawTermName = ''Raw.Type'
          , rawBindingName = ''Raw.TypeBinders'
          , rawScopeName = ''Raw.ScopedType'
          , rawVarConName = 'Raw.TypeVar
          , rawSubTermNames = [ ''Raw.OpArgTyping' ]
          } ]
  , freeFoilNameModifier = id
  , freeFoilScopeNameModifier = ("Scoped" ++ )
  , freeFoilConNameModifier = id
  , signatureNameModifier = (++ "Sig")
  , ignoreNames = []
  }

deriving instance GHC.Generic (Term'Sig a scope term)
deriving instance GHC.Generic (OpArg'Sig a scope term)
deriving instance GHC.Generic (Type'Sig a scope term)
deriveGenericK ''Term'Sig
deriveGenericK ''OpArg'Sig
deriveGenericK ''Type'Sig

deriving instance Functor (Term'Sig a scope)
deriving instance Functor (OpArg'Sig a scope)
deriving instance Functor (Type'Sig a scope)
deriveBifunctor ''OpArg'Sig
deriveBifunctor ''Term'Sig
deriveBifunctor ''Type'Sig

instance Foil.CoSinkable  (Binders' a)  -- FIXME: derive via GenericK?

-- | Ignore 'Raw.BNFC'Position' when matching terms.
instance ZipMatchK Raw.BNFC'Position where zipMatchWithK = zipMatchViaChooseLeft
-- | Match 'Raw.OpIdent' via 'Eq'.
instance ZipMatchK Raw.OpIdent where zipMatchWithK = zipMatchViaEq
-- | Match 'Raw.MetaVarIdent' via 'Eq'.
instance ZipMatchK Raw.MetaVarIdent where zipMatchWithK = zipMatchViaEq

instance ZipMatchK a => ZipMatchK (Term'Sig a)
instance ZipMatchK a => ZipMatchK (OpArg'Sig a)
instance ZipMatchK a => ZipMatchK (Type'Sig a)

instance ZipMatchK a => ZipMatch (Term'Sig a) where zipMatch = genericZipMatch2
instance ZipMatchK a => ZipMatch (Type'Sig a) where zipMatch = genericZipMatch2

-- * User-defined code

type Subst = Subst' Raw.BNFC'Position Foil.VoidS
type Term = Term' Raw.BNFC'Position

lookupSubst :: Raw.MetaVarIdent -> [Subst] -> Maybe Subst
lookupSubst m = find $ \(Subst _loc m' _ _) -> m == m'

applySubsts :: Foil.Distinct n => Foil.Scope n -> [Subst] -> Term n -> Term n
applySubsts scope substs term =
  case term of
    MetaVar _loc m args | Just (Subst _ _ binders body) <- lookupSubst m substs ->
      substitutePattern scope Foil.emptyNameMap binders args body
    Var{} -> term
    Node node -> Node (bimap goScoped (applySubsts scope substs) node)
  where
    goScoped (ScopedAST binders body) =
      case Foil.assertDistinct binders of
        Foil.Distinct ->
          let scope' = Foil.extendScopePattern binders scope
           in ScopedAST binders (applySubsts scope' substs body)

-- | A SOAS interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pTermTyping (Raw.tokens input) of
    Left err -> do
      putStrLn err
      exitFailure
    Right typing -> putStrLn (Raw.printTree typing)
