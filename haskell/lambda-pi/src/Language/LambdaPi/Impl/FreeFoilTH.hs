{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
module Language.LambdaPi.Impl.FreeFoilTH where

import           Control.Monad.Free.Foil.TH
import qualified Language.LambdaPi.Syntax.Abs    as Raw

-- * Generated code

-- ** Signature
mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
