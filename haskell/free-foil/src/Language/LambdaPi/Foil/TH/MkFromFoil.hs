{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH.MkFromFoil (mkFromFoil) where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil
import Data.Coerce (coerce)

mkFromFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkFromFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  let fromFoilTBody = NormalB (LamCaseE (map fromMatchFoilTerm termCons))
  let fromFoilPatternBody = NormalB (LamCaseE (map fromMatchFoilPattern patternCons))
  let fromFoilScopedBody = NormalB (LamCaseE (map fromMatchFoilScoped scopeCons))

  return [
    SigD fromFoilTermT $ fromFunctionSign [n]                -- forall n .
      (AppT (ConT foilTermT) (VarT n))  -- -> FoilTerm n 
      (ConT termT)                      -- -> Term
    , FunD fromFoilTermT [Clause [] fromFoilTBody []]

    , SigD fromFoilPatternT $ fromFunctionSign [n,l]                            -- forall n l.
      (foldl AppT (ConT foilPatternT) [VarT n, VarT l]) -- -> FoilPattern n l
      (ConT patternT)                                   -- -> Pattern
    , FunD fromFoilPatternT [Clause [] fromFoilPatternBody []]

    , SigD fromFoilScopedTermT $ fromFunctionSign [n]              -- forall n .
      (AppT (ConT foilScopeT) (VarT n)) -- -> FoilScopedTerm n 
      (ConT scopeT)                     -- -> ScopedTerm
    , FunD fromFoilScopedTermT [Clause [] fromFoilScopedBody []]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    fromFoilTermT = mkName ("fromFoil" ++ nameBase termT)
    fromFoilPatternT = mkName ("fromFoil" ++ nameBase patternT)
    fromFoilScopedTermT = mkName ("fromFoil" ++ nameBase scopeT)

    fromFunctionSign :: [Name] -> Type -> Type -> Type
    fromFunctionSign forallNames from to = 
      ForallT (map (`PlainTV` SpecifiedSpec) forallNames) []
        (AppT (AppT ArrowT from) to)

    fromMatchFoilTerm :: Con -> Match
    fromMatchFoilTerm (NormalC conName params) =
      let matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
          conTypes = map snd params
      in Match matchPat (matchBody conTypes matchPat conName) []

      where
        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName ("varName" ++ show n)):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Name -> Body
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

        toExpr :: Type -> Pat -> Exp
        toExpr (ConT tyName) (VarP patName)
          | tyName == nameT = AppE (VarE 'coerce) (AppE (VarE 'Foil.ppName) (VarE patName))
          | tyName == patternT = AppE (VarE fromFoilPatternT) (VarE patName)
          | tyName == scopeT = AppE (VarE fromFoilScopedTermT) (VarE patName)
          | tyName == termT = AppE (VarE fromFoilTermT) (VarE patName)
          | otherwise = VarE patName

    fromMatchFoilPattern :: Con -> Match
    fromMatchFoilPattern (NormalC conName params) =
      let
        matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
        conTypes = map snd params
      in Match matchPat (matchBody conTypes matchPat conName) []

      where
        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = ConP (mkName "UnsafeNameBinder") [] [VarP (mkName $ "binder" ++ show n)]:toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Name -> Body
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

        toExpr :: Type -> Pat -> Exp
        toExpr _ (ConP _ _ [VarP varName]) = AppE (VarE 'coerce) (AppE (VarE 'Foil.ppName) (VarE varName)) 
        toExpr (ConT typeN) (VarP patName) 
          | typeN == patternT = AppE (VarE fromFoilPatternT) (VarE patName)
          | otherwise = VarE patName

    fromMatchFoilScoped :: Con -> Match
    fromMatchFoilScoped (NormalC conName params) =
      let
        matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
        conTypes = map snd params
      in Match matchPat (matchBody conTypes matchPat conName) []

      where
        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = WildP:toPats (n+1) types  -- in the case fo using: VarP (mkName ("varName" ++ show n))
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Name -> Body
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

        toExpr :: Type -> Pat -> Exp
        toExpr (ConT tyName) (VarP patName)
          | tyName == termT = AppE (VarE fromFoilTermT) (VarE patName)
          | otherwise = VarE patName