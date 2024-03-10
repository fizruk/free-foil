{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Language.LambdaPi.Foil.Example where

import Language.LambdaPi.Foil
import Language.LambdaPi.Foil.TH
import Unsafe.Coerce (unsafeCoerce)


class CoSinkable (pattern :: S -> S -> *) where
  coSinkabilityProof
    :: (Name n -> Name n')
    -> pattern n l
    -> (forall l'. (Name l -> Name l') -> pattern n' l' -> r)
    -> r

instance CoSinkable NameBinder where
  coSinkabilityProof _rename (UnsafeNameBinder name) cont = cont unsafeCoerce (UnsafeNameBinder name)

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
  :: Distinct n => Distinct l
  => Scope n
  -> Substitution Term n l
  -> Pattern n l
  -> (forall k. Distinct k => Pattern n k -> Substitution Term n k -> Scope l -> r)
  -> r
withPattern scope subst pat cont =
  case pat of
    PatternVar var ->
      withFresh scope $ \binder ->
        let scope' = extendScope binder scope
            subst' = addRename (sink subst) var (nameOf binder)
            pat' = PatternVar binder
        in cont pat' subst' scope'

    PatternPair pat1 pat2 ->
      withPattern scope subst pat1 $ \pat1' subst' scope' ->
        withPattern scope' subst' pat2 $ \pat2' subst'' scope'' ->
          let pat' = PatternPair pat1' pat2'
          in cont pat' subst'' scope''

    PatternWildcard -> error "no idea what to do here"

substTerm
  :: Distinct o => Scope o -> Substitution Term i o -> Term i -> Term o
substTerm scope subst = \case
  Var x -> lookupSubst subst x
  Pair l r -> Pair (substTerm scope subst l) (substTerm scope subst r)
  App f x -> App (substTerm scope subst f) (substTerm scope subst x)
  Lam pat body -> withPattern scope subst pat (\pattern' subst' scope' ->
    let body' = substitute scope' subst' body
    in Lam pattern' body')
  Pi pat typ body -> withPattern scope subst pat (\pattern' subst' scope' ->
    let body' = substitute scope' subst' body
    in Pi pattern' typ body')
  Universe -> Universe


