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
module Language.SOAS.Impl.Generated where

import Data.Bifunctor.TH
import qualified Data.Map as Map
import Data.String (IsString(..))
import qualified Control.Monad.Foil as Foil
import           Control.Monad.Free.Foil.TH.MkFreeFoil
import qualified Language.SOAS.Syntax.Abs    as Raw
import qualified Language.SOAS.Syntax.Lex    as Raw
import qualified Language.SOAS.Syntax.Par    as Raw
import qualified Language.SOAS.Syntax.Print  as Raw
import Data.ZipMatchK
import Generics.Kind.TH (deriveGenericK)
import Language.SOAS.FreeFoilConfig (soasConfig)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import qualified Language.SOAS.Syntax.Abs as Raw
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

mkFreeFoil soasConfig

deriveGenericK ''OpArg'Sig
deriveGenericK ''Term'Sig
deriveGenericK ''OpArgTyping'Sig
deriveGenericK ''Type'Sig
deriveGenericK ''Subst'
deriveGenericK ''Constraint'
deriveGenericK ''OpTyping'
deriveGenericK ''Binders'
deriveGenericK ''TypeBinders'

deriveBifunctor ''OpArg'Sig
deriveBifunctor ''Term'Sig
deriveBifunctor ''OpArgTyping'Sig
deriveBifunctor ''ScopedOpArgTyping'Sig
deriveBifunctor ''Type'Sig

instance Foil.Sinkable (Subst' a)
instance Foil.Sinkable (Constraint' a)
instance Foil.Sinkable (OpTyping' a)

instance Foil.SinkableK (Binders' a)
instance Foil.SinkableK (TypeBinders' a)

instance Foil.HasNameBinders (Binders' a)
instance Foil.CoSinkable (Binders' a)

instance Foil.HasNameBinders (TypeBinders' a)
instance Foil.CoSinkable (TypeBinders' a)

data Test a (n :: Foil.S) (l :: Foil.S) where
  Good1 :: Foil.NameBinder n l -> Test a n l
  Good2 :: Foil.NameBinder n n -> Test a n n
  Good3 :: Test a n n
  Good4 :: Foil.NameBinder n i -> Test a i l -> Test a n l
  Good5 :: Foil.NameBinder n i' -> Test a i' i -> Test a i l -> Test a n l
  -- Bad1 :: Test a n l                           -- not enough binders
  -- Bad2 :: Foil.NameBinder n i -> Test a n l    -- intermediate scope escapes (not enough binders?)
  -- Bad3 :: Int -> Int -> Int -> Foil.NameBinder i n -> Int -> Test a n l    -- unexpected scope extension
  -- Bad4 :: Foil.NameBinder l n -> Test a n l    -- unexpected scope extension
  -- Bad5 :: Foil.NameBinder n i -> Foil.NameBinder i l -> Foil.NameBinder l i -> Test a n l -- intermediate scope escapes (not enough binders?)
  -- Bad6 :: Foil.NameBinder n l -> Foil.NameBinder n l -> Test a n l -- unexpected scope extension
  -- Bad7 :: [Foil.NameBinder n l] -> Test a n l -- no GHasNameBinders (unreadable error message)
deriveGenericK ''Test
instance Foil.HasNameBinders (Test a)
instance Foil.SinkableK (Test a)
instance Foil.CoSinkable (Test a)


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

-- |
-- >>> "?m[App(Lam(x.x), Lam(y.y))]" :: Term' Raw.BNFC'Position Foil.VoidS
-- ?m [App (Lam (x0 . x0), Lam (x0 . x0))]
-- >>> "Lam(y. Let(Lam(x. x), f. ?m[y, App(f, y)]))" :: Term' Raw.BNFC'Position Foil.VoidS
-- Lam (x0 . Let (Lam (x1 . x1), x1 . ?m [x0, App (x1, x0)]))
instance IsString (Term' Raw.BNFC'Position Foil.VoidS) where
  fromString = toTerm' Foil.emptyScope Map.empty . unsafeParse Raw.pTerm

instance IsString (Type' Raw.BNFC'Position Foil.VoidS) where
  fromString = toType' Foil.emptyScope Map.empty . unsafeParse Raw.pType

-- |
-- >>> "Lam : ∀ a b. (a.b) → a→b" :: OpTyping' Raw.BNFC'Position Foil.VoidS
-- Lam : ∀ x0 x1 . (x0 . x1) → x0 → x1
instance IsString (OpTyping' Raw.BNFC'Position Foil.VoidS) where
  fromString = toOpTyping' Foil.emptyScope Map.empty . unsafeParse Raw.pOpTyping

-- |
-- >>> "?m[x y] ↦ App(y, x)" :: Subst' Raw.BNFC'Position Foil.VoidS
-- ?m [x0 x1] ↦ App (x1, x0)
instance IsString (Subst' Raw.BNFC'Position Foil.VoidS) where
  fromString = toSubst' Foil.emptyScope Map.empty . unsafeParse Raw.pSubst

-- |
-- >>> "∀ x y. ?m[x, y] = App(y, x)" :: Constraint' Raw.BNFC'Position Foil.VoidS
-- ∀ x0 x1 . ?m [x0, x1] = App (x1, x0)
instance IsString (Constraint' Raw.BNFC'Position Foil.VoidS) where
  fromString = toConstraint' Foil.emptyScope Map.empty . unsafeParse Raw.pConstraint

instance Show (Term' a n) where show = Raw.printTree . fromTerm'
instance Show (Type' a n) where show = Raw.printTree . fromType'
instance Show (Subst' a n) where show = Raw.printTree . fromSubst'
instance Show (Constraint' a n) where show = Raw.printTree . fromConstraint'
instance Show (OpTyping' a n) where show = Raw.printTree . fromOpTyping'

-- * User-defined helpers

unsafeParse :: ([Raw.Token] -> Either String a) -> String -> a
unsafeParse parse input =
  case parse (Raw.myLexer input) of
    Left err -> error err
    Right x -> x
