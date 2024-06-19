{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
module Language.LambdaPi.Impl.FreeFoilTH where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.TH
import           Data.Bifunctor.TH
import           Data.Map                     (Map)
import qualified Language.LambdaPi.Syntax.Abs as Raw

-- * Generated code

-- ** Signature
mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
deriveBifunctor ''Term'Sig
deriveBifoldable ''Term'Sig
deriveBitraversable ''Term'Sig

-- ** Pattern synonyms
mkPatternSynonyms ''Term'Sig

-- ** Conversion

mkConvertToFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
mkConvertFromFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- * User-defined code

-- | Convert 'Raw.Term'' into a scope-safe representation.
-- This is a special case of 'convertToAST'.
toTerm' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> AST (Term'Sig a) n
toTerm' = convertToAST convertToTerm'Sig getPattern'Binder getTerm'FromScopedTerm'

-- | Convert a scope-safe representation back into 'Raw.Term''.
-- This is a special case of 'convertFromAST'.
--
-- 'Raw.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromTerm' :: AST (Term'Sig a) n -> Raw.Term' a
fromTerm' = convertFromAST
  convertFromTerm'Sig
  (Raw.Var (error "location missing"))
  (Raw.PatternVar (error "location missing"))
  (Raw.AScopedTerm (error "location missing"))
  (\n -> Raw.VarIdent ("x" ++ show n))
