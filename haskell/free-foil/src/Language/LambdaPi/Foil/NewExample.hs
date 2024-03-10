
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Language.LambdaPi.Foil.NewExample where

import Language.LambdaPi.Foil
import Unsafe.Coerce (unsafeCoerce)

data Pattern (n :: S) (l :: S) where
  PatternWildcard :: Pattern n n
  PatternVar      :: NameBinder n l -> Pattern n l
  PatternPair     :: Pattern n l -> Pattern l k -> Pattern n k

instance CoSinkable Pattern where
  coSinkabilityProof rename pattern cont =
    case pattern of
      PatternWildcard -> cont rename PatternWildcard
      PatternVar binder ->
        coSinkabilityProof rename binder $ \ rename' binder' ->
          cont rename' (PatternVar binder')
      PatternPair l r ->
        coSinkabilityProof rename l $ \ renameL l' ->
          coSinkabilityProof renameL r $ \ renameR r' ->
            cont renameR (PatternPair l' r')

extendRenaming
     :: CoSinkable pattern
     => (Name n -> Name n')
     -> pattern n l
     -> (forall l'. (Name l -> Name l') -> pattern n' l' -> r)
     -> r
extendRenaming _rename pattern cont =
     cont unsafeCoerce (unsafeCoerce pattern)

data Term (n :: S) where
  Var  :: Name n -> Term n
  Pair :: Term n -> Term n -> Term n
  App  :: Term n -> Term n -> Term n
  Lam  :: Pattern n l -> Term l -> Term n
  Pi   :: Pattern n l -> Term n -> Term l -> Term n
  Universe :: Term n


instance Sinkable Term where
     sinkabilityProof :: (Name n -> Name l) -> Term n -> Term l
     sinkabilityProof rename = \case
       Var x -> Var (rename x)
       Pair l r -> Pair (sinkabilityProof rename l) (sinkabilityProof rename r)
       App fun arg -> App (sinkabilityProof rename fun) (sinkabilityProof rename arg)
       Lam pat body -> coSinkabilityProof rename pat $ \rename' pat' ->
         Lam pat' (sinkabilityProof rename' body)
       Pi pat argType retType -> coSinkabilityProof rename pat $ \rename' pat' ->
         Pi pat' (sinkabilityProof rename argType) (sinkabilityProof rename' retType)
       Universe -> Universe

withPattern
  :: DExt s o
  => Scope o
  -> Pattern n i
  -> Substitution Term n s
  -> (forall o'. Distinct o' => Pattern o o' -> Substitution Term i o' -> Scope o' -> r)
  -> r
withPattern scope pat subst cont =
  case pat of
    PatternWildcard -> cont PatternWildcard (sink subst) scope

    PatternVar var ->
      withRefreshed scope (nameOf var) $ \ var' ->
        let pat' = PatternVar var'
            subst' = addRename (sink subst) var (sink (nameOf var'))
            scope' = extendScope var' scope
        in cont pat' subst' scope'

    PatternPair p1 p2 ->
      withPattern scope p1 subst $ \p1' subst' scope' ->
        withPattern scope' p2 subst' $ \p2' subst'' scope'' ->
          cont (PatternPair p1' p2') subst'' scope''

substTerm
  :: Distinct o => Scope o -> Substitution Term i o -> Term i -> Term o
substTerm scope subst = \case
  Var x -> lookupSubst subst x
  Pair l r -> Pair (substTerm scope subst l) (substTerm scope subst r)
  App f x -> App (substTerm scope subst f) (substTerm scope subst x)
  Lam pat body -> withPattern scope pat subst $ \pattern' subst' scope' ->
    let body' = substTerm scope' subst' body
    in Lam pattern' body'
  Pi pat typ body -> withPattern scope pat subst $ \pattern' subst' scope' ->
    let body' = substTerm scope' subst' body
        typ' = substTerm scope subst typ
    in Pi pattern' typ'  body'
  Universe -> Universe
