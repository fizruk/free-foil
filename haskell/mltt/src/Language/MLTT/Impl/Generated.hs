{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
-- | Everything about MLTT that is /generated/ rather than written.
--
-- The scope-safe term type, the signature bifunctor, the pattern synonyms and
-- the conversions to and from the raw (BNFC) syntax all come out of
-- 'mkFreeFoil' and 'mkFreeFoilConversions'. What is written by hand here is
-- only the instances that the generated types need and Template Haskell cannot
-- supply: the 'Generics.Kind.GenericK' representations, the bifunctor
-- instances of the signature, and the pattern instances of 'Pattern''.
module Language.MLTT.Impl.Generated where

import           Control.Monad.Free.Foil                 (convertFromASTWith)
import           Control.Monad.Free.Foil.TH.MkFreeFoil
import qualified Control.Monad.Foil                    as Foil
import           Data.Bifunctor.TH
import qualified Data.Map                              as Map
import           Data.String                           (IsString (..))
import           Data.ZipMatchK
import           Data.ZipMatchK.TH                     (deriveZipMatchK2)
import           Generics.Kind.TH                      (deriveGenericK)
import           Language.MLTT.FreeFoilConfig          (mlttConfig, rawScopedTerm,
                                                        rawVar)
import qualified Language.MLTT.Syntax.Abs              as Raw
import qualified Language.MLTT.Syntax.Layout           as Raw
import qualified Language.MLTT.Syntax.Lex              as Raw
import qualified Language.MLTT.Syntax.Par              as Raw
import qualified Language.MLTT.Syntax.Print            as Raw

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import qualified Data.Map as Map
-- >>> import qualified Language.MLTT.Syntax.Par as Par
-- >>> import qualified Language.MLTT.Syntax.Abs as Raw

-- * Generated code

mkFreeFoil mlttConfig

deriveGenericK ''Term'Sig
deriveGenericK ''Pattern'

deriveBifunctor ''Term'Sig
deriveBifoldable ''Term'Sig
deriveBitraversable ''Term'Sig

instance Foil.SinkableK (Pattern' a)
instance Foil.HasNameBinders (Pattern' a)
instance Foil.CoSinkable (Pattern' a)

mkFreeFoilConversions mlttConfig

-- | Ignore 'Raw.BNFC'Position' when matching terms.
instance ZipMatchK Raw.BNFC'Position where zipMatchWithK = zipMatchViaChooseLeft

-- | Match the signature with the derived (rather than the generic) instance:
-- matching terms is most of what a type checker does, and the generic instance
-- reflects a node into its "Generics.Kind" representation on every comparison.
deriveZipMatchK2 ''Term'Sig

-- | Two patterns are unified by their binders, in order.
--
-- Note that this is the /default/ instance, so it deliberately ignores the
-- pattern constructors: @(x, y)@ and a hypothetical single pattern binding two
-- names would unify. For MLTT that is the intended reading, since what the body
-- of a binder may refer to is exactly the names the pattern binds.
instance Foil.UnifiablePattern (Pattern' a)

-- | Ignore source positions when unifying patterns.
instance Foil.UnifiableInPattern Raw.BNFC'Position where
  unifyInPattern _ _ = True

-- * Parsing and printing

-- | Parse a raw term, calling 'error' if it does not parse.
unsafeParse :: ([Raw.Token] -> Either String a) -> String -> a
unsafeParse parse input =
  case parse (Raw.tokens input) of
    Left err -> error ("could not parse an MLTT term: " <> input <> "\n  " <> err)
    Right x  -> x

-- | Parse a raw program: a sequence of modules, laid out.
parseProgram :: String -> Either String Raw.Program
parseProgram input = Raw.pProgram (Raw.resolveLayout True (Raw.tokens input))

-- |
-- >>> "λ x ⇒ λ y ⇒ x" :: Term' Raw.BNFC'Position Foil.VoidS
-- λ x0 ⇒ λ x1 ⇒ x0
--
-- >>> "Π (A : 𝕌) → Π (x : A) → A" :: Term' Raw.BNFC'Position Foil.VoidS
-- Π (x0 : 𝕌) → Π (x1 : x0) → x0
--
-- Pattern binders bind more than one name at a time:
--
-- >>> "λ (x, y) ⇒ y" :: Term' Raw.BNFC'Position Foil.VoidS
-- λ (x0, x1) ⇒ x1
--
-- The range-parametric conversion allocates the binders it introduces inside
-- the given range, so the same source elaborates to the same term whatever
-- else the ambient scope holds:
--
-- >>> toTerm'In (Foil.NameRange 50 59) Foil.emptyScope Map.empty (unsafeParse Par.pTerm "λ x ⇒ λ y ⇒ x")
-- λ x50 ⇒ λ x51 ⇒ x50
instance IsString (Term' Raw.BNFC'Position Foil.VoidS) where
  fromString = toTerm' Foil.emptyScope Map.empty . unsafeParse Raw.pTerm

instance Show (Term' a n) where show = Raw.printTree . fromTerm'

-- | Convert back to raw syntax, naming free and bound variables separately.
--
-- A variable free in the whole term is named from a 'Foil.NameMap'; a bound one
-- is named from its index. Keeping the two apart matters because raw names are
-- not unique across scope indices: a definition\'s body is elaborated before
-- the definition\'s own name is allocated, so @def f := λ x ⇒ x@ gives both @f@
-- and the @x@ it binds the raw name 0.
fromTermWith
  :: Foil.Distinct n
  => (Int -> Raw.VarIdent)          -- ^ Name a bound variable, from its index.
  -> Foil.NameMap n Raw.VarIdent    -- ^ Name a variable free in the whole term.
  -> Term' a n
  -> Raw.Term' a
fromTermWith bound names =
  convertFromASTWith fromTerm'Sig rawVar fromPattern' rawScopedTerm
    (`Foil.lookupName` names) bound

-- | Print a term, naming free and bound variables separately.
showTermWith
  :: Foil.Distinct n
  => (Int -> Raw.VarIdent) -> Foil.NameMap n Raw.VarIdent -> Term' a n -> String
showTermWith bound names = Raw.printTree . fromTermWith bound names

-- | 'fromTermWith', with one naming function covering both the binder
-- occurrences (through the generated 'fromPattern'With') and the
-- bound-variable references.
fromTermNamed
  :: Foil.Distinct n
  => (Int -> Raw.VarIdent) -> Foil.NameMap n Raw.VarIdent -> Term' a n -> Raw.Term' a
fromTermNamed bound names =
  convertFromASTWith fromTerm'Sig rawVar (fromPattern'With bound) rawScopedTerm
    (`Foil.lookupName` names) bound

-- | Print a term with one naming function for everything bound.
showTermNamed
  :: Foil.Distinct n
  => (Int -> Raw.VarIdent) -> Foil.NameMap n Raw.VarIdent -> Term' a n -> String
showTermNamed bound names = Raw.printTree . fromTermNamed bound names

-- * Convenient monomorphic synonyms
--
-- Everything downstream is written against terms annotated with a source
-- position, which is what the parser produces.

-- | A scope-safe MLTT term, annotated with a source position.
type Term = Term' Raw.BNFC'Position

-- | A scope-safe MLTT pattern, annotated with a source position.
type Pattern = Pattern' Raw.BNFC'Position

-- | A scope-safe MLTT term under a binder, annotated with a source position.
type ScopedTerm = ScopedTerm' Raw.BNFC'Position
