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
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst (identitySubst VarE) binder arg
        in whnf scope (substitute scope subst body)
      fun' -> AppE fun' arg
  t -> t

-- | Compute normal form (NF) of a \(\lambda\)-term.
nf :: Distinct n => Scope n -> Expr n -> Expr n
nf scope expr = case expr of
  LamE binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in LamE binder (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst =  addSubst (identitySubst VarE ) binder arg
        in nf scope (substitute scope subst body)
      fun' -> AppE (nf scope fun') (nf scope arg)
  t -> t

-- | Compute normal form (NF) of a __closed__ \(\lambda\)-term.
nf' :: Expr VoidS -> Expr VoidS
nf' = nf emptyScope
