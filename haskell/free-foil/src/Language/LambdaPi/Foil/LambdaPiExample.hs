{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
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
import Language.LambdaPi.Foil.TH
import Language.LambdaPi.LambdaPi.Abs
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map as Map

mkFoilData ''Term ''VarIdent ''ScopedTerm ''Pattern
mkToFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkFromFoil ''Term ''VarIdent ''ScopedTerm ''Pattern
mkInstancesFoil ''Term ''VarIdent ''ScopedTerm ''Pattern

eval :: Distinct n => Scope n -> FoilTerm n -> FoilTerm n
eval scope = \case 
  FoilLam FoilPatternWildcard (FoilAScopedTerm body) -> eval scope body
  FoilLam (FoilPatternVar binder) (FoilAScopedTerm body) -> 
      let scope' = extendScope binder scope
        in FoilLam (FoilPatternVar binder) (FoilAScopedTerm (eval scope' body))
  FoilLam (FoilPatternPair binder1 binder2) (FoilAScopedTerm body) ->
      let scope'' = extendScope binder2 (extendScope binder1 scope)
        in FoilLam (FoilPatternPair binder1 binder2) (FoilAScopedTerm (eval scope'' body))
  FoilPi FoilPatternWildcard term (FoilAScopedTerm body) -> eval scope body
  FoilPi pattern@(FoilPatternVar binder) term (FoilAScopedTerm body) -> 
    let scope' = extendScope binder scope
        termReduced = eval scope term 
        bodyReduced = eval scope' body 
      in reduce scope (FoilPi pattern termReduced (FoilAScopedTerm bodyReduced))
  FoilPi pattern@(FoilPatternPair binder1 binder2) term (FoilAScopedTerm body) -> 
    let scope'' = extendScope binder2 (extendScope binder1 scope)
        termReduced = eval scope term
        bodyReduced = eval scope'' body 
      in reduce scope (FoilPi pattern termReduced (FoilAScopedTerm bodyReduced))
  FoilApp f args -> 
    let fReduced = eval scope f
        argsReduced = eval scope args
      in reduce scope (FoilApp fReduced argsReduced) 
  FoilVar name -> FoilVar name
  FoilPair term1 term2 -> FoilPair (eval scope term1) (eval scope term2)
  x -> x


reduce :: Distinct n => Scope n -> FoilTerm n -> FoilTerm n
reduce scope = \case
  FoilApp f x ->
    case reduce scope f of
      FoilLam pattern (FoilAScopedTerm body) -> case pattern of
        FoilPatternWildcard -> body
        FoilPatternVar binder -> case x of
          FoilVar name ->
            let substitution = UnsafeSubstitution FoilVar (Map.insert (ppName (nameOf binder)) x Map.empty)
            in substitute scope substitution body
          _ -> FoilApp (FoilLam pattern (FoilAScopedTerm body)) x
        FoilPatternPair binder1 binder2 ->  case x of
          FoilPair (FoilVar name1) (FoilVar name2) ->
            let substitution = UnsafeSubstitution FoilVar (Map.fromList [(ppName (nameOf binder1), FoilVar name1),
                                                                          (ppName (nameOf binder2), FoilVar name2)])
            in substitute scope substitution body
          _ -> FoilApp (FoilLam pattern (FoilAScopedTerm body)) x
      func -> FoilApp func x
  FoilPi pattern term (FoilAScopedTerm body) -> case pattern of
    FoilPatternWildcard -> body
    FoilPatternVar binder -> case term of
      FoilVar name ->
        let substitution = UnsafeSubstitution FoilVar (Map.insert (ppName (nameOf binder)) term Map.empty)
        in substitute scope substitution body
      _ -> FoilPi pattern term (FoilAScopedTerm body)
    FoilPatternPair binder1 binder2 ->  case term of
      FoilPair (FoilVar name1) (FoilVar name2) ->
        let substitution = UnsafeSubstitution FoilVar (Map.fromList [(ppName (nameOf binder1), FoilVar name1),
                                                                      (ppName (nameOf binder2), FoilVar name2)])
        in substitute scope substitution body
      _ -> FoilPi pattern term (FoilAScopedTerm body)
  term -> term

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