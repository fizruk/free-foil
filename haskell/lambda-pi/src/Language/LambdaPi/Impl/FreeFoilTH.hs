{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.LambdaPi.Impl.FreeFoilTH where

import           Control.Monad.Free.Foil.TH
import qualified Language.LambdaPi.Syntax.Abs    as Raw

-- * Generated code

-- ** Signature
mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- ** Pattern synonyms
mkPatternSynonyms ''Term'Sig
