{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
-- | Example implementation of untyped \(\lambda\)-calculus with the foil.
module Control.Monad.Free.Foil.Example where

import           Control.Monad.Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor.TH

-- | Untyped \(\lambda\)-terms in scope @n@.
data ExprF scope term
  -- | Application of one term to another: \((t_1, t_2)\)
  = AppF term term
  -- | \(\lambda\)-abstraction introduces a binder and a term in an extended scope: \(\lambda x. t\)
  | LamF scope
  deriving (Functor)
deriveBifunctor ''ExprF

pattern AppE :: AST ExprF n -> AST ExprF n -> AST ExprF n
pattern AppE x y = Node (AppF x y)

pattern LamE :: NameBinder n l -> AST ExprF l -> AST ExprF n
pattern LamE binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, AppE, LamE #-}

type Expr = AST ExprF

-- | Use 'ppExpr' to show \(\lambda\)-terms.
instance Show (Expr n) where
  show = ppExpr

-- | Compute weak head normal form (WHNF) of a \(\lambda\)-term.
--
-- >>> whnf emptyScope (AppE (churchN 2) (churchN 2))
-- λx1. (λx0. λx1. (x0 (x0 x1)) (λx0. λx1. (x0 (x0 x1)) x1))
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> AppE fun' arg
  t -> t

-- | Compute weak head normal form (WHNF) of a __closed__ \(\lambda\)-term.
--
-- >>> whnf' (AppE (churchN 2) (churchN 2))
-- λx1. (λx0. λx1. (x0 (x0 x1)) (λx0. λx1. (x0 (x0 x1)) x1))
whnf' :: Expr VoidS -> Expr VoidS
whnf' = whnf emptyScope

-- | Compute normal form (NF) of a \(\lambda\)-term.
--
-- >>> nf emptyScope (AppE (churchN 2) (churchN 2))
-- λx1. λx2. (x1 (x1 (x1 (x1 x2))))
nf :: Distinct n => Scope n -> Expr n -> Expr n
nf scope expr = case expr of
  LamE binder body ->
    -- Instead of using 'assertDistinct',
    -- another option is to add 'Distinct l' constraint
    -- to the definition of 'LamE'.
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in LamE binder (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst identitySubst binder arg
        in nf scope (substitute scope subst body)
      fun' -> AppE (nf scope fun') (nf scope arg)
  t -> t

-- | Compute normal form (NF) of a __closed__ \(\lambda\)-term.
--
-- >>> nf' (AppE (churchN 2) (churchN 2))
-- λx1. λx2. (x1 (x1 (x1 (x1 x2))))
nf' :: Expr VoidS -> Expr VoidS
nf' = nf emptyScope

-- | Pretty print a name.
ppName :: Name n -> String
ppName name = "x" <> show (nameId name)

-- | Pretty-print a \(\lambda\)-term.
--
-- >>> ppExpr (churchN 3)
-- "\955x0. \955x1. (x0 (x0 (x0 x1)))"
ppExpr :: Expr n -> String
ppExpr = \case
  Var name -> ppName name
  AppE x y -> "(" <> ppExpr x <> " " <> ppExpr y <> ")"
  LamE binder body -> "λ" <> ppName (nameOf binder) <> ". " <> ppExpr body

-- | A helper for constructing \(\lambda\)-abstractions.
lam :: Distinct n => Scope n -> (forall l. DExt n l => Scope l -> NameBinder n l -> Expr l) -> Expr n
lam scope mkBody = withFresh scope $ \x ->
  let scope' = extendScope x scope
   in LamE x (mkBody scope' x)

-- | Church-encoding of a natural number \(n\).
--
-- >>> churchN 0
-- λx0. λx1. x1
--
-- >>> churchN 3
-- λx0. λx1. (x0 (x0 (x0 x1)))
churchN :: Int -> Expr VoidS
churchN n =
  lam emptyScope $ \sx nx ->
    lam sx $ \_sxy ny ->
      let x = sink (Var (nameOf nx))
          y = Var (nameOf ny)
       in iterate (AppE x) y !! n
