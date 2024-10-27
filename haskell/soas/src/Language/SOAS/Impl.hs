{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints -ddump-splices #-}
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
deriveBifunctor ''ScopedOpArgTyping'Sig
deriveBifunctor ''Type'Sig

-- FIXME: derive via GenericK
instance Foil.CoSinkable (Binders' a) where
  coSinkabilityProof rename (NoBinders loc) cont = cont rename (NoBinders loc)
  -- coSinkabilityProof rename (OneBinder loc binder) cont =
  --   Foil.coSinkabilityProof rename binder $ \rename' binder' ->
  --     cont rename' (OneBinder loc binder')
  coSinkabilityProof rename (SomeBinders loc binder binders) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      Foil.coSinkabilityProof rename' binders $ \rename'' binders' ->
        cont rename'' (SomeBinders loc binder' binders')

  withPattern withBinder unit comp scope binders cont =
    case binders of
      NoBinders loc -> cont unit (NoBinders loc)
      -- OneBinder loc binder ->
      --   Foil.withPattern withBinder unit comp scope binder $ \f binder' ->
      --     cont f (OneBinder loc binder')
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

type Constraint = Constraint' Raw.BNFC'Position Foil.VoidS
type Subst = Subst' Raw.BNFC'Position Foil.VoidS
type Term = Term' Raw.BNFC'Position
type Type = Type' Raw.BNFC'Position
type OpTyping = OpTyping' Raw.BNFC'Position Foil.VoidS

-- ** From raw to scope-safe

-- >>> "?m[App(Lam(x.x), Lam(y.y))]" :: Term
-- ?m [App (. Lam (x0 . x0), . Lam (x0 . x0))]
-- >>> "Lam(y. Let(Lam(x. x), f. ?m[y, App(f, y)]))" :: SOAS.Term Foil.VoidS
-- Lam (x0 . Let (Lam (x1 . x1), x1 . ?m [x0, App (x1, x0)]))
instance IsString (Term' Raw.BNFC'Position Foil.VoidS) where
  fromString = toTerm' Foil.emptyScope Map.empty . unsafeParse Raw.pTerm

instance IsString (Type' Raw.BNFC'Position Foil.VoidS) where
  fromString = toType' Foil.emptyScope Map.empty . unsafeParse Raw.pType

-- >>> "Lam : ∀ a b. (a.b) → a→b" :: SOAS.OpTyping
-- Lam : ∀ x0 x1 . (x0 . x1) → x0 → x1
instance IsString (OpTyping' Raw.BNFC'Position Foil.VoidS) where
  fromString = toOpTyping' Foil.emptyScope Map.empty . unsafeParse Raw.pOpTyping

-- >>> "?m[x y] ↦ App(y, x)" :: SOAS.Subst
-- ?m [x0 x1] ↦ App (x1, x0)
instance IsString (Subst' Raw.BNFC'Position Foil.VoidS) where
  fromString = toSubst' Foil.emptyScope Map.empty . unsafeParse Raw.pSubst

-- >>> "∀ x y. ?m[x, y] = App(y, x)" :: SOAS.Constraint
-- ∀ x0 x1 . ?m [x0, x1] = App (x1, x0)
instance IsString (Constraint' Raw.BNFC'Position Foil.VoidS) where
  fromString = toConstraint' Foil.emptyScope Map.empty . unsafeParse Raw.pConstraint

-- ** From scope-safe to raw

instance Show (Term' a n) where show = Raw.printTree . fromTerm'
instance Show (Type' a n) where show = Raw.printTree . fromType'
instance Show (Subst' a n) where show = Raw.printTree . fromSubst'
instance Show (Constraint' a n) where show = Raw.printTree . fromConstraint'
instance Show (OpTyping' a n) where show = Raw.printTree . fromOpTyping'

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

-- * Helpers

unsafeParse :: ([Raw.Token] -> Either String a) -> String -> a
unsafeParse parse input =
  case parse (Raw.myLexer input) of
    Left err -> error err
    Right x -> x
