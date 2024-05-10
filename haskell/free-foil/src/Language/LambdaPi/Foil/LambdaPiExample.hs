{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
-- {-# OPTIONS_GHC -Wno-name-shadowing #-} -- Убрать
-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Убрать
module Language.LambdaPi.Foil.LambdaPiExample where

import Language.LambdaPi.Foil (Scope(..), Name (UnsafeName), NameBinder(UnsafeNameBinder)
                            , Distinct, Substitution(..), extendScope, addRename
                            , sink, lookupSubst, withRefreshed, S(..), Distinct(..)
                            , ppName, nameOf, Sinkable(..), CoSinkable(..))
import qualified Language.LambdaPi.Foil as Foil
import Language.LambdaPi.Foil.TH
import Language.LambdaPi.LambdaPi.Abs
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map as Map

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern

withRefreshedPattern :: Distinct o => Scope o ->  Substitution FoilTerm i o -> FoilPattern i l
  -> (forall o' . Foil.DExt o o' => FoilPattern o o' -> Substitution FoilTerm l o' -> Scope o' -> r) -> r 
withRefreshedPattern scope subst FoilPatternWildcard cont = cont FoilPatternWildcard (Foil.sink subst) scope
withRefreshedPattern scope subst (FoilPatternVar binder) cont = withRefreshed scope (nameOf binder) (\binder' -> 
  let subst' = addRename (sink subst) binder (nameOf binder')
      scope' = extendScope binder' scope
    in cont (FoilPatternVar binder') subst' scope')
withRefreshedPattern scope subst (FoilPatternPair pattern1 pattern2) cont = 
  withRefreshedPattern scope subst pattern1 (\pattern1' subst' scope' -> 
    withRefreshedPattern scope' subst' pattern2 (\pattern2' subst'' scope'' -> 
      cont (FoilPatternPair pattern1' pattern2') subst'' scope''))

substitute :: Distinct o => Scope o -> Substitution FoilTerm i o -> FoilTerm i -> FoilTerm o
substitute scope subst = \case
    FoilVar name -> lookupSubst subst name
    FoilApp f x -> FoilApp (substitute scope subst f) (substitute scope subst x)
    FoilLam pattern (FoilAScopedTerm body) -> case pattern of
      foilPattern -> withRefreshedPattern scope subst foilPattern (\pattern' subst' scope'->
        let body' = substitute scope' subst' body in FoilLam pattern' (FoilAScopedTerm body'))
    FoilPi pattern term (FoilAScopedTerm body) -> case pattern of
      foilPattern -> withRefreshedPattern scope subst foilPattern (\pattern' subst' scope'->
        let body' = substitute scope' subst' body 
            term' = substitute scope subst term
          in FoilPi pattern' term' (FoilAScopedTerm body'))
    FoilPair a b -> FoilPair (substitute scope subst a) (substitute scope subst b)

whnf :: Distinct n => Scope n -> FoilTerm n -> FoilTerm n
whnf scope = go
  where
    go = \case
      FoilApp fun arg -> 
        case whnf scope fun of 
          FoilLam pattern (FoilAScopedTerm body) -> whnf scope $
            substitute scope (patternBindings scope pattern arg) body
          t -> t
      t@FoilLam{} -> t
      t@FoilPi{} -> t
      t@FoilVar{} -> t
      FoilPair l r -> FoilPair (go l) (go r)


patternBindings :: Distinct n => Scope n -> FoilPattern n l -> FoilTerm n -> Substitution FoilTerm l n
patternBindings _ FoilPatternWildcard _ = Foil.identitySubst FoilVar
patternBindings _ (FoilPatternVar x) term = Foil.addSubst (Foil.identitySubst FoilVar) x term
patternBindings scope (FoilPatternPair f s) term =
  case whnf scope term of
    FoilPair f' s' -> 
      let fSubst = patternBindings scope f f' -- Scope n -> FoilPattern n l1 -> FoilTerm n -> Substitution FoilTerm l1 n -- withPattern
          s'' = extendFoilTerm scope f s' -- Scope n -> FoilPattern n l1 -> FoilTerm n -> FoilTerm l1
          scope' = extendScopePattern scope f -- Scope n -> FoilPattern n l1 -> Scope l1
          sSubst = patternBindings scope' s s'' -- Scope l1 -> FoilPattern l1 l -> FoilTerm l1 -> Substitution FoilTerm l l1
        in combineSubsts scope fSubst sSubst
      -- withRefreshedPattern scope (Foil.identitySubst FoilVar) f (\_ fSubst' scope' -> 
      --   withRefreshedPattern scope' fSubst' s (\_ sSubst' scope' -> 
      --     combineSubsts scope fSubst' sSubst' -- fSubst' :=: Substitution FoilTerm l1 o' | sSubst' :=: Substitution FoilTerm l o'1
      --   )
      -- )
    _ -> error "trying ro pattern match non-pair as a pair"
    where
      extendFoilTerm :: Scope n -> FoilPattern n l -> FoilTerm n -> FoilTerm l
      extendFoilTerm _ _ = unsafeCoerce

extendScopePattern :: Scope n -> FoilPattern n l -> Scope l
extendScopePattern scope FoilPatternWildcard = scope
extendScopePattern scope (FoilPatternVar x) = extendScope x scope
extendScopePattern scope (FoilPatternPair f s) =
  let firstExtend = extendScopePattern scope f
    in extendScopePattern firstExtend s

combineSubsts :: Distinct n => Scope n -> Substitution FoilTerm l1 n -> Substitution FoilTerm l l1 -> Substitution FoilTerm l n
combineSubsts scope firstSubst@(UnsafeSubstitution f env1) (UnsafeSubstitution _ env2) =
  UnsafeSubstitution f (Map.unionWith (\_ s -> s) env1 (Map.map (substitute scope firstSubst) env2))



-- Language.LambdaPi.Foil.LambdaPiExample.substitute Language.LambdaPi.Foil.LambdaPiExample.scope1 Language.LambdaPi.Foil.LambdaPiExample.substitution Language.LambdaPi.Foil.LambdaPiExample.foilLam
foilLam :: FoilTerm n
foilLam = FoilLam
            (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
            (FoilAScopedTerm (FoilLam
                                (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
                                (FoilAScopedTerm (FoilApp
                                                    (FoilVar (UnsafeName "s"))
                                                    (FoilApp
                                                      (FoilVar (UnsafeName "s"))
                                                      (FoilVar (UnsafeName "s")))))))

emptyScope :: Scope VoidS
emptyScope = UnsafeScope []

foilTerm :: FoilTerm n
foilTerm = FoilVar (UnsafeName "aa" :: Name n)

substitution :: Substitution FoilTerm i o
substitution = UnsafeSubstitution FoilVar (Map.insert "s" foilTerm Map.empty)

-- Language.LambdaPi.Foil.LambdaPiExample.reduce Language.LambdaPi.Foil.LambdaPiExample.emptyScope Language.LambdaPi.Foil.LambdaPiExample.reduceFoilExample
reduceFoilExample :: FoilTerm n
reduceFoilExample = FoilApp
                      (FoilLam
                        (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
                        (FoilAScopedTerm (FoilApp
                                            (FoilVar (UnsafeName "s"))
                                            (FoilVar (UnsafeName "s")))))
                      (FoilVar (UnsafeName "a"))

-- Language.LambdaPi.Foil.LambdaPiExample.reduce Language.LambdaPi.Foil.LambdaPiExample.emptyScope Language.LambdaPi.Foil.LambdaPiExample.reducePiExample
reducePiExample :: FoilTerm n
reducePiExample = FoilPi
                    (FoilPatternVar (UnsafeNameBinder (UnsafeName "s")))
                    (FoilVar (UnsafeName "a"))
                    (FoilAScopedTerm (FoilApp
                                        (FoilVar (UnsafeName "s"))
                                        (FoilVar (UnsafeName "s"))))

reducePiExample2 :: FoilTerm n
reducePiExample2 = FoilApp (FoilVar (UnsafeName "a")) (FoilVar (UnsafeName "a"))