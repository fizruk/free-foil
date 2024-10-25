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
import Data.Map (Map)
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
  , freeFoilConvertFromName = ("from" ++ )
  , freeFoilConvertToName = ("to" ++ )
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

toBinders' :: Foil.Distinct n =>
  Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Binders' a ->
    (forall l. Foil.DExt n l => Foil.Scope l -> Map Raw.VarIdent (Foil.Name l) -> Binders' a n l -> r)
    -> r
toBinders' scope env rawBinders cont =
  case rawBinders of
    Raw.NoBinders loc -> cont scope env (NoBinders loc)
    Raw.SomeBinders loc x xs ->
      Foil.withFresh scope $ \binder ->
        let scope' = Foil.extendScope binder scope
            env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
        in toBinders' scope' env' xs $ \scope'' env'' binders ->
            cont scope'' env'' (SomeBinders loc binder binders)

toOpArg' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.OpArg' a -> OpArg' a n
toOpArg' scope env = \case
  Raw.OpArg loc binders (Raw.ScopedTerm _loc body) ->
    toBinders' scope env binders $ \scope' env' binders' ->
      OpArg loc binders' (toTerm' scope' env' body)

toTerm' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> Term' a n
toTerm' scope env = \case
  Raw.Var _loc x ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing -> error ("undefined variable: " ++ Raw.printTree x)
  Raw.Op loc op args ->
    Op loc op (map (toOpArg' scope env) args)
  Raw.MetaVar loc m args ->
    MetaVar loc m (map (toTerm' scope env) args)

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

-- fromOpArg'Sig :: OpArg'Sig a (Raw.Binders' a, Raw.ScopedTerm' a) (Raw.Term' a) -> Raw.OpArg' a
-- fromOpArg'Sig (OpArgSig loc (binders, body)) = Raw.OpArg loc binders body

-- fromTerm'Sig :: Term'Sig a (Raw.Binders' a, Raw.ScopedTerm' a) (Raw.Term' a) -> Raw.Term' a
-- fromTerm'Sig = \case
--   OpSig loc op args -> Raw.Op loc op (map fromOpArg'Sig args)
--   MetaVarSig loc m args -> Raw.MetaVar loc m args

fromBinders' :: (Int -> Raw.VarIdent) -> Binders' a n l -> Raw.Binders' a
fromBinders' mkIdent = \case
  NoBinders loc -> Raw.NoBinders loc
  SomeBinders loc binder binders ->
    Raw.SomeBinders loc
      (mkIdent (Foil.nameId (Foil.nameOf binder)))
      (fromBinders' mkIdent binders)

fromTerm' :: Term' a n -> Raw.Term' a
fromTerm' = convertFromAST
  fromTerm'Sig
  (Raw.Var (error "trying to access an erased annotation on a variable"))
  fromBinders'
  (Raw.ScopedTerm (error "trying to access an erased annotation on a scoped term"))
  (\i -> Raw.VarIdent ("x" <> show i))

instance Show (Term' a n) where
  show = Raw.printTree . fromTerm'

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
