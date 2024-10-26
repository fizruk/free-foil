{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts         #-}
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
import qualified Data.Map as Map
import Data.String (IsString(..))
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
import Language.SOAS.FreeFoilConfig (soasConfig)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

mkFreeFoil soasConfig

deriveGenericK ''OpArg'Sig
deriveGenericK ''Term'Sig
deriveGenericK ''OpArgTyping'Sig
deriveGenericK ''Type'Sig

deriveBifunctor ''OpArg'Sig
deriveBifunctor ''Term'Sig
deriveBifunctor ''OpArgTyping'Sig
deriveBifunctor ''Type'Sig

-- FIXME: derive via GenericK
instance Foil.CoSinkable (Binders' a) where
  coSinkabilityProof rename (NoBinders loc) cont = cont rename (NoBinders loc)
  coSinkabilityProof rename (SomeBinders loc binder binders) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      Foil.coSinkabilityProof rename' binders $ \rename'' binders' ->
        cont rename'' (SomeBinders loc binder' binders')

  withPattern withBinder unit comp scope binders cont =
    case binders of
      NoBinders loc -> cont unit (NoBinders loc)
      SomeBinders loc binder moreBinders ->
        Foil.withPattern withBinder unit comp scope binder $ \f binder' ->
          let scope' = Foil.extendScopePattern binder' scope
           in Foil.withPattern withBinder unit comp scope' moreBinders $ \g moreBinders' ->
                cont (comp f g) (SomeBinders loc binder' moreBinders')

-- FIXME: derive via GenericK
instance Foil.CoSinkable (TypeBinders' a) where
  coSinkabilityProof rename (NoTypeBinders loc) cont = cont rename (NoTypeBinders loc)
  coSinkabilityProof rename (SomeTypeBinders loc binder binders) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      Foil.coSinkabilityProof rename' binders $ \rename'' binders' ->
        cont rename'' (SomeTypeBinders loc binder' binders')

  withPattern withBinder unit comp scope binders cont =
    case binders of
      NoTypeBinders loc -> cont unit (NoTypeBinders loc)
      SomeTypeBinders loc binder moreTypeBinders ->
        Foil.withPattern withBinder unit comp scope binder $ \f binder' ->
          let scope' = Foil.extendScopePattern binder' scope
           in Foil.withPattern withBinder unit comp scope' moreTypeBinders $ \g moreTypeBinders' ->
                cont (comp f g) (SomeTypeBinders loc binder' moreTypeBinders')

mkFreeFoilConversions soasConfig

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

-- ** From raw to scope-safe

-- >>> "?m[App(.Lam(x.x), .Lam(y.y))]" :: Term
-- ?m [App (. Lam (x0 . x0), . Lam (x0 . x0))]
instance IsString (Term' Raw.BNFC'Position Foil.VoidS) where
  fromString = toTerm' Foil.emptyScope Map.empty . unsafeParseRawTerm
    where
      unsafeParseRawTerm input =
        case Raw.pTerm (Raw.myLexer input) of
          Left err -> error err
          Right term -> term

-- ** From scope-safe to raw

instance Show (Term' a n) where show = Raw.printTree . fromTerm'
instance Show (Subst' a n) where show = Raw.printTree . fromSubst'

-- ** Meta variable substitutions

-- | Lookup a substitution by its 'Raw.MetaVarIdent'.
lookupSubst :: Raw.MetaVarIdent -> [Subst] -> Maybe Subst
lookupSubst m = find $ \(Subst _loc m' _ _) -> m == m'

-- | Apply meta variable substitutions to a term.
applySubsts :: Foil.Distinct n => Foil.Scope n -> [Subst] -> Term n -> Term n
applySubsts scope substs term =
  case term of
    MetaVar _loc m args | Just (Subst _ _ binders body) <- lookupSubst m substs ->
      substitutePattern scope Foil.voidSubst binders args body
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
