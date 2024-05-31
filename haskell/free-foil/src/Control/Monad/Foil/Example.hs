{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | Example implementation of untyped \(\lambda\)-calculus with the foil.
module Control.Monad.Foil.Example where

import           Control.DeepSeq
import           Control.Monad.Foil

-- | Untyped \(\lambda\)-terms in scope @n@.
data Expr n where
  -- | Variables are names in scope @n@: \(x\)
  VarE :: Name n -> Expr n
  -- | Application of one term to another: \((t_1, t_2)\)
  AppE :: Expr n -> Expr n -> Expr n
  -- | \(\lambda\)-abstraction introduces a binder and a term in an extended scope: \(\lambda x. t\)
  LamE :: NameBinder n l -> Expr l -> Expr n

-- | Use 'ppExpr' to show \(\lambda\)-terms.
instance Show (Expr n) where
  show = ppExpr

instance NFData (Expr l) where
  rnf (LamE binder body) = rnf binder `seq` rnf body
  rnf (AppE fun arg)     = rnf fun `seq` rnf arg
  rnf (VarE name)        = rnf name

-- | This instance serves as a proof
-- that sinking of 'Expr' is safe.
instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder $ \rename' binder' ->
    LamE binder' (sinkabilityProof rename' body)

-- | Substitution for untyped \(\lambda\)-terms.
-- The foil helps implement this function without forgetting scope extensions and renaming.
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) $ \binder' ->
      let subst' = addRename (sink subst) binder (nameOf binder')
          scope' = extendScope binder' scope
          body' = substitute scope' subst' body
       in LamE binder' body'

-- | Compute weak head normal form (WHNF) of a \(\lambda\)-term.
--
-- >>> whnf emptyScope (AppE (churchN 2) (churchN 2))
-- λx1. (λx0. λx1. (x0 (x0 x1)) (λx0. λx1. (x0 (x0 x1)) x1))
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst (identitySubst VarE) binder arg
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
        let subst = addSubst (identitySubst VarE) binder arg
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
  VarE name -> ppName name
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
      let x = sink (VarE (nameOf nx))
          y = VarE (nameOf ny)
       in iterate (AppE x) y !! n
