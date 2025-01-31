{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
module Language.Lambda.Impl.FreeFoilTH where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Foil.TH
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.TH
import           Data.Bifunctor.TH
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.String                     (IsString (..))
import           Data.ZipMatchK
import           Generics.Kind.TH                (deriveGenericK)
import qualified GHC.Generics                    as GHC
import qualified Language.Lambda.Syntax.Abs    as Raw
import qualified Language.Lambda.Syntax.Lex    as Raw
import qualified Language.Lambda.Syntax.Par    as Raw
import qualified Language.Lambda.Syntax.Print  as Raw


-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

-- ** Signature
mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
deriveBifunctor ''Term'Sig
deriveBifoldable ''Term'Sig
deriveBitraversable ''Term'Sig

-- ** Pattern synonyms
mkPatternSynonyms ''Term'Sig

-- ** Conversion helpers

mkConvertToFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
mkConvertFromFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- ** Scope-safe patterns

mkFoilPattern ''Raw.VarIdent ''Raw.Pattern'
deriveGenericK ''FoilPattern'
instance Foil.SinkableK (FoilPattern' a)
instance Foil.HasNameBinders (FoilPattern' a)
instance Foil.CoSinkable (FoilPattern' a)
mkToFoilPattern ''Raw.VarIdent ''Raw.Pattern'
mkFromFoilPattern ''Raw.VarIdent ''Raw.Pattern'

instance Foil.UnifiablePattern (FoilPattern' a)
-- | Ignoring location information when unifying patterns.
instance Foil.UnifiableInPattern Raw.BNFC'Position where
  unifyInPattern _ _  = True

-- | Deriving 'GHC.Generic' and 'GenericK' instances.
deriving instance GHC.Generic (Term'Sig a scope term)
deriveGenericK ''Term'Sig

-- -- | Match 'Raw.Ident' via 'Eq'.
-- instance ZipMatchK Raw.Ident where zipMatchWithK = zipMatchViaEq

-- | Ignore 'Raw.BNFC'Position' when matching terms.
instance ZipMatchK Raw.BNFC'Position where zipMatchWithK = zipMatchViaChooseLeft

-- | Generic 'ZipMatchK' instance.
instance ZipMatchK a => ZipMatchK (Term'Sig a)

-- * User-defined code

-- | Generic annotated scope-safe \(\lambda\Pi\)-terms with patterns.
type Term' a = AST (FoilPattern' a) (Term'Sig a)

-- | Scode-safe \(\lambda\Pi\)-terms annotated with source code position.
type Term = Term' Raw.BNFC'Position

-- | Scope-safe patterns annotated with source code position.
type FoilPattern = FoilPattern' Raw.BNFC'Position

-- ** Conversion helpers

-- | Convert 'Raw.Term'' into a scope-safe term.
-- This is a special case of 'convertToAST'.
toTerm' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> Term' a n
toTerm' = convertToAST convertToTerm'Sig toFoilPattern' getTerm'FromScopedTerm'

-- | Convert 'Raw.Term'' into a closed scope-safe term.
-- This is a special case of 'toTerm''.
toTerm'Closed :: Raw.Term' a -> Term' a Foil.VoidS
toTerm'Closed = toTerm' Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'Raw.Term''.
-- This is a special case of 'convertFromAST'.
--
-- 'Raw.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromTerm' :: Term' a n -> Raw.Term' a
fromTerm' = convertFromAST
  convertFromTerm'Sig
  (Raw.Var (error "location missing"))
  (fromFoilPattern' mkVarIdent)
  (Raw.AScopedTerm (error "location missing"))
  mkVarIdent
  where
    mkVarIdent n = Raw.VarIdent ("x" ++ show n)

-- | Parse scope-safe terms via raw representation.
--
-- >>> fromString "λx.λy.λx.x" :: Term Foil.VoidS
-- λ x0 . λ x1 . λ x2 . x2
instance IsString (AST FoilPattern (Term'Sig Raw.BNFC'Position) Foil.VoidS) where
  fromString input = case Raw.pTerm (Raw.tokens input) of
    Left err   -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
    Right term -> toTerm'Closed term

-- | Pretty-print scope-safe terms via raw representation.
instance Show (AST (FoilPattern' a) (Term'Sig a) Foil.VoidS) where
  show = Raw.printTree . fromTerm'

-- ** Evaluation

-- | Match a pattern against an term.
matchPattern :: FoilPattern n l -> Term n -> Foil.Substitution Term l n
matchPattern pat term = go pat term Foil.identitySubst
  where
    go :: FoilPattern i l -> Term n -> Foil.Substitution Term i n -> Foil.Substitution Term l n
    go (FoilPatternVar _loc x) e    = \subst -> Foil.addSubst subst x e

whnf :: Foil.Distinct n => Foil.Scope n -> Term n -> Term n
whnf scope = \case
  App loc f x ->
    case whnf scope f of
      Lam _loc binder body ->
        let subst = matchPattern binder x
         in whnf scope (substitute scope subst body)
      f' -> App loc f' x
  t -> t

-- "λx. x"