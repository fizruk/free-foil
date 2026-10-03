{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | The laws for the λ-calculus of "Control.Monad.Foil.Example", the plain
-- foil without the free monad: its hand-written 'Foil.Sinkable' instance,
-- its relative monad ('rbind'), and its 'F.substitute'. Terms are
-- generated and compared through the free foil version of the same
-- language, which has the same constructors.
module Control.Monad.Foil.ExampleLawsSpec (spec) where

import           Test.Hspec

import qualified Control.Monad.Foil                    as Foil
import qualified Control.Monad.Foil.Example            as F
import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil               (AST (..))
import qualified Control.Monad.Free.Foil.Example       as FF
import           Control.Monad.Free.Foil.ExampleSyntax (exprSyntax)
import           Control.Monad.Free.Foil.Laws.Mirror

-- | The free foil term with the same structure.
toAST :: F.Expr n -> FF.Expr n
toAST = \case
  F.VarE x      -> Var x
  F.AppE f x    -> FF.AppE (toAST f) (toAST x)
  F.LamE b body -> FF.LamE b (toAST body)

-- | The plain foil term with the same structure.
fromAST :: FF.Expr n -> F.Expr n
fromAST = \case
  Var x          -> F.VarE x
  FF.AppE f x    -> F.AppE (fromAST f) (fromAST x)
  FF.LamE b body -> F.LamE b (fromAST body)

mirror :: Mirror Foil.NameBinder FF.ExprF F.Expr
mirror = Mirror
  { mirrorSyntax = exprSyntax genNameBinder nameBinderNames
  , mirrorFrom = fromAST
  , mirrorTo = toAST
  , mirrorSubstitute = F.substitute
  , mirrorAlphaEquiv = Nothing
  }

spec :: Spec
spec = mirrorSpec mirror $ \cls -> \case
  MirrorSinkAgreesWithLiftRM | cls /= Inclusions -> KnownFailure
    "extendRenaming is a coercion, so free names under a binder are not renamed"
  _ -> Holds
