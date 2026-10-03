{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | The untyped λ-calculus of "Control.Monad.Free.Foil.Example", made ready
-- for the law tests: the instances its signature lacks, and its
-- 'SyntaxGen'.
module Control.Monad.Free.Foil.ExampleSyntax (exprSyntax) where

import           Data.Bifunctor.TH               (deriveBifoldable, deriveBitraversable)

import           Control.Monad.Foil.Laws         (GenPattern)
import           Control.Monad.Free.Foil.Example (ExprF (..))
import           Control.Monad.Free.Foil.Laws    (SyntaxGen (..))
import           Data.ZipMatchK.TH               (deriveZipMatchK)

deriveBifoldable ''ExprF
deriveBitraversable ''ExprF
deriveZipMatchK ''ExprF

-- | The λ-calculus, with a given kind of pattern.
exprSyntax :: GenPattern binder -> SyntaxGen binder ExprF
exprSyntax genPat = SyntaxGen
  { sgShapes = [AppF () (), LamF ()]
  , sgPattern = genPat
  , sgShowNode = \case
      AppF f x  -> "(" <> f <> " " <> x <> ")"
      LamF body -> body
  }
