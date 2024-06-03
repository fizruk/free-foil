{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Control.Monad.Foil.TH.MkFromFoil (mkFromFoil) where

import           Language.Haskell.TH

import qualified Control.Monad.Foil  as Foil
import           Data.Coerce         (coerce)

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
    SigD fromFoilTermT (ForallT [PlainTV n SpecifiedSpec] []
    (AppT (AppT ArrowT
      (AppT ListT (AppT (ConT ''Foil.Name) (VarT n)))) -- [VarIdent]  -- fresh identifiers
    (AppT (AppT ArrowT
      (AppT (ConT foilTermT) (VarT n))) -- FoilTerm n
      (ConT termT)) -- Term
    ))
    , FunD fromFoilTermT [Clause [] fromFoilTBody []]

    , SigD fromFoilPatternT (ForallT ([PlainTV n SpecifiedSpec, PlainTV l SpecifiedSpec]) []
    (AppT (AppT ArrowT
      (foldl AppT (ConT foilPatternT) ([VarT n, VarT l]))) -- FoilPattern n t1..tn l
      (ConT patternT)) -- Pattern
    )
    , FunD fromFoilPatternT [Clause [] fromFoilPatternBody []]

    , SigD fromFoilScopedTermT (ForallT [PlainTV n SpecifiedSpec] []
    (AppT (AppT ArrowT
      (AppT (ConT foilScopeT) (VarT n))) -- FoilScopedTerm n
      (ConT scopeT)) -- ScopedTerm
    )
    , FunD fromFoilScopedTermT [Clause [] fromFoilScopedBody []]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    fromFoilTermT = mkName ("fromFoil" ++ nameBase termT)
    fromFoilPatternT = mkName ("fromFoil" ++ nameBase patternT)
    fromFoilScopedTermT = mkName ("fromFoil" ++ nameBase scopeT)

    maxBinderNumber :: [Con] -> Int
    maxBinderNumber cons = maximum (map
        (\case
            (NormalC _ params) -> (getBinderNumber (map snd params) 0)
            _ -> 0
        ) cons)

    generateNames :: Int -> Int -> [Name]
    generateNames from to
      | from >= to = []
      | otherwise = mkName ("t" ++ show from) : generateNames (from + 1) to

    getBinderNumber :: [Type] -> Int -> Int
    getBinderNumber [] counter = counter
    getBinderNumber ((ConT tyName):types) counter
      | tyName == nameT = getBinderNumber types (counter + 1)
      | otherwise = getBinderNumber types counter

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
          | tyName == nameT = ConP (mkName "UnsafeNameBinder") [] [VarP (mkName $ "binder" ++ show n)]:toPats (n+1) types -- change to WildP
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Name -> Body
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

        toExpr :: Type -> Pat -> Exp
        toExpr _ (ConP _ _ [VarP varName]) =
          AppE (VarE 'coerce) (VarE varName) -- Уязвимость: mkName (nameBase nameT) предполагает что имя конструктора совпадает с именем типа. Но нет возможности выбрать подходищай конструктор так как непонятно как паттернматчить аргумент конструктора с нужным
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
          | tyName == nameT = VarP (mkName ("varName" ++ show n)):toPats (n+1) types -- change to WildP
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
          | tyName == nameT = AppE (VarE 'coerce) (VarE patName)
          | tyName == patternT = AppE (VarE fromFoilPatternT) (VarE patName)
          | tyName == scopeT = AppE (VarE fromFoilScopedTermT) (VarE patName)
          | tyName == termT = AppE (VarE fromFoilTermT) (VarE patName)
          | otherwise = VarE patName
