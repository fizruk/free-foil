{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}
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
                            , sink, lookupSubst, withRefreshed, emptyScope
                            , nameOf, Sinkable(..), CoSinkable(..))
import Language.LambdaPi.Foil.TH
import Language.LambdaPi.LambdaPi.Abs
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map as Map

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern


substitute :: Distinct o => Scope o -> Substitution FoilTerm i o -> FoilTerm i -> FoilTerm o
substitute scope subst = \case
    FoilVar name -> lookupSubst subst name
    FoilApp f x -> FoilApp (substitute scope subst f) (substitute scope subst x)
    FoilLam pattern (FoilAScopedTerm body) -> case pattern of
      FoilPatternWildcard -> let
        body' = substitute scope subst body in FoilLam FoilPatternWildcard (FoilAScopedTerm body')
      FoilPatternVar binder -> withRefreshed scope (nameOf binder) (\binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body
          in FoilLam (FoilPatternVar binder') (FoilAScopedTerm body')
        )
      FoilPatternPair binder1 binder2 -> withRefreshed scope (nameOf binder1) (\binder1' ->
        let subst' = addRename (sink subst) binder1 (nameOf binder1')
            scope' = extendScope binder1' scope in withRefreshed scope' (nameOf binder2) (\binder2' ->
              let subst'' = addRename (sink subst') binder2 (nameOf binder2')
                  scope'' = extendScope binder2' scope'
                  body'' = substitute scope'' subst'' body
                in FoilLam (FoilPatternPair binder1' binder2') (FoilAScopedTerm body'')
              )
        )
    FoilPi pattern term (FoilAScopedTerm body) -> case pattern of
      FoilPatternWildcard -> let
        body' = substitute scope subst body
        term' = substitute scope subst term in FoilPi FoilPatternWildcard term' (FoilAScopedTerm body')
      FoilPatternVar binder -> withRefreshed scope (nameOf binder) (\binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body
            term' = substitute scope subst term
          in FoilPi (FoilPatternVar binder') term' (FoilAScopedTerm body')
        )
      FoilPatternPair binder1 binder2 -> withRefreshed scope (nameOf binder1) (\binder1' ->
        let subst' = addRename (sink subst) binder1 (nameOf binder1')
            scope' = extendScope binder1' scope in withRefreshed scope' (nameOf binder2)  (\binder2' ->
              let subst'' = addRename (sink subst') binder2 (nameOf binder2')
                  scope'' = extendScope binder2' scope'
                  body'' = substitute scope'' subst'' body
                  term'' = substitute scope subst term
                in FoilPi (FoilPatternPair binder1' binder2') term'' (FoilAScopedTerm body'')
              )
        )
    FoilPair a b -> FoilPair (substitute scope subst a) (substitute scope subst b)

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

scope1 :: Scope o
scope1 = UnsafeScope ["s"]

foilTerm :: FoilTerm n
foilTerm = FoilVar (UnsafeName "aa" :: Name n)

substitution :: Substitution FoilTerm i o
substitution = UnsafeSubstitution FoilVar (Map.insert "s" foilTerm Map.empty)

-- two :: Term
-- two = Lam (PatternVar "s") (AScopedTerm (Lam (PatternVar "z") (AScopedTerm (App (Var "s") (App (Var "s") (Var "z"))))))

-- func :: VarIdent -> Name n
-- func (VarIdent s) = UnsafeName s :: Name n

-- substed = FoilLam (FoilPatternVar (UnsafeNameBinder (UnsafeName "z"))) (FoilAScopedTerm (FoilApp (FoilVar (UnsafeName "zz")) (FoilApp (FoilVar (UnsafeName "zz")) (FoilVar (UnsafeName "z")))))

-- -- Language.LambdaPi.Foil.LambdaPiExample.toFoilTerm Language.LambdaPi.Foil.LambdaPiExample.func Language.LambdaPi.Foil.emptyScope Language.LambdaPi.Foil.LambdaPiExample.two
