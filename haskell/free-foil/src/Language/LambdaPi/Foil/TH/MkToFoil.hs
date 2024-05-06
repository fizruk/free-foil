{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH.MkToFoil (mkToFoil) where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil
import Data.Maybe (fromJust)


mkToFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkToFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  let toFoilTBody = NormalB (LamCaseE (map toMatchTerm termCons))
  let toFoilScopedBody = NormalB (LamCaseE (map toFoilScopedMatch scopeCons))
  let withPatternBody = NormalB (CaseE (VarE (mkName "pat")) (map withPatternMatch patternCons))

  return [
    SigD toFoilScopedT (toFoilScopedSigType n)
    , FunD toFoilScopedT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilScopedBody []]

    , SigD withPatternT (withPatternSigType n l)
    , FunD withPatternT [Clause [VarP withPatternToNameArg, VarP withPatternScopeArg, VarP withPatternPatArg, VarP withPatternContArg] withPatternBody []]

    , SigD toFoilTermT (toFoilTermSigType n)
    , FunD toFoilTermT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilTBody []]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toFoilTermT = mkName ("toFoil" ++ nameBase termT)
    toFoilScopedT = mkName ("toFoil" ++ nameBase scopeT)
    withPatternT = mkName "withPattern"

    withPatternToNameArg = mkName "toName"
    withPatternScopeArg = mkName "scope"
    withPatternPatArg = mkName "pat"
    withPatternContArg = mkName "cont"


    withPatternSigType :: Name -> Name -> Type
    withPatternSigType n l =
      ForallT [PlainTV n SpecifiedSpec, PlainTV rName SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
        (AppT (AppT ArrowT varIdentToNameN) --(VarIdent -> Name n) 
        (AppT (AppT ArrowT scopeN) -- Scope n
        (AppT (AppT ArrowT (ConT patternT)) -- Pattern
        (AppT (AppT ArrowT contType) (VarT rName)
        ))))
        where
          rName = mkName "r"
          varIdentToNameN = AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n))
          scopeN = AppT (ConT (mkName "Scope")) (VarT n)
          contType =
            ForallT [PlainTV l SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT l)]  -- forall l. Distinct l
              (AppT (AppT ArrowT foilPatternNL) -- FoilPattern n l
              (AppT (AppT ArrowT varIdentToNameL) -- (VarIdent -> Name l)
              (AppT (AppT ArrowT scopeL) (VarT rName)))) -- Scope l -> r
              where
                foilPatternNL = foldl AppT (ConT foilPatternT) [VarT n, VarT l]
                varIdentToNameL = AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT l))
                scopeL = AppT (ConT (mkName "Scope")) (VarT l)

    toFoilTermSigType :: Name -> Type
    toFoilTermSigType n =
      ForallT [PlainTV n SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
        (AppT (AppT ArrowT varIdentToName) -- (VarIdent -> Name n)
        (AppT (AppT ArrowT scopeN) -- Scope n
        (AppT (AppT ArrowT (ConT termT)) foilTermN) -- Term -> FoilTerm n
        ))
      where
        varIdentToName = AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n))
        scopeN = AppT (ConT (mkName "Scope")) (VarT n)
        foilTermN = AppT (ConT foilTermT) (VarT n)


    toFoilScopedSigType :: Name -> Type
    toFoilScopedSigType n =
      ForallT [PlainTV n SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
        (AppT (AppT ArrowT varIdentToName) -- (VarIdent -> Name n)
        (AppT (AppT ArrowT scopeN) -- Scope n
        (AppT (AppT ArrowT (ConT scopeT)) foilScopedTermN) -- ScopedTerm -> FoilScopedTerm n
        ))
      where
        varIdentToName = AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n))
        scopeN = AppT (ConT (mkName "Scope")) (VarT n)
        foilScopedTermN = AppT (ConT foilScopeT) (VarT n)


    toFoilScopedMatch :: Con -> Match
    toFoilScopedMatch (NormalC conName params) =
      let
        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params
      in Match matchPat (matchBody conTypes matchPat) []

      where
        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Body
        matchBody matchTypes (ConP name _ matchParams) =
          NormalB (foldl AppE (ConE $ mkName ("Foil" ++ nameBase name)) (zipWith toExpr matchTypes matchParams))

          where
            toExpr :: Type -> Pat -> Exp
            toExpr (ConT tyName) (VarP patName)
              | tyName == termT = AppE (AppE (AppE (VarE toFoilTermT) (VarE (mkName "toName"))) (VarE (mkName "scope"))) (VarE patName)
              | otherwise = VarE patName

    withPatternMatch :: Con -> Match
    withPatternMatch (NormalC conName params) =
      Match matchPat (matchBody conTypes matchPat) []
      where
        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params
        foilConstrName = mkName ("Foil" ++ nameBase conName)

        matchBody :: [Type] -> Pat -> Body
        matchBody matchTypes (ConP _ _ matchParams) =
          NormalB (matchBodyExpr 0 matchTypes matchParams)
          where
            finalToNameName = mkName "toName'"
            finalScopeName = mkName "scope'"
            finalPatName = mkName "pat'"

            letPat = LetE [
              ValD (VarP finalPatName) (NormalB (foldl AppE (ConE foilConstrName) (foilConNames 0 matchTypes matchParams))) []
              ] applyConWithPat

            applyConWithPat
              | countNames conTypes == 0 = foldl AppE (VarE withPatternContArg) [VarE finalPatName, VarE withPatternToNameArg, VarE withPatternScopeArg]
              | otherwise = foldl AppE (VarE withPatternContArg) [VarE finalPatName, VarE finalToNameName, VarE finalScopeName]

            matchBodyExpr :: Int -> [Type] -> [Pat] -> Exp
            matchBodyExpr _ [] [] = letPat
            matchBodyExpr index ((ConT tyName):types) ((VarP varName):pats)
              | tyName == nameT =
                AppE (AppE (VarE 'Foil.withFresh) (VarE prevScopeName))
                  (LamE [VarP newBinderName]
                    (LetE [
                      ValD (VarP newScopeName) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE newBinderName, VarE prevScopeName])) [],
                      FunD newToNameName
                        [Clause [VarP xName]
                          (GuardedB [
                            (NormalG (AppE (AppE (VarE (mkName "==")) (VarE xName)) (VarE varName)), AppE (VarE 'Foil.nameOf) (VarE newBinderName)),
                            (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE prevToNameName) (VarE xName)))
                          ]) []]
                    ] (matchBodyExpr (index+1) types pats)))
              | tyName == patternT =
                foldl AppE (VarE withPatternT) [VarE prevToNameName, VarE prevScopeName, VarE varName,
                  LamE [VarP newVarName, VarP newToNameName, VarP newScopeName] (matchBodyExpr (index+1) types pats)
                ]
              | otherwise = matchBodyExpr (index+1) types pats
              where
                newBinderName = mkName ("binder" ++ show index)
                newScopeName = if null types && null pats then finalScopeName else mkName ("scope" ++ show index)
                prevScopeName = mkName ("scope" ++ (if index > 0 then show $ index-1 else ""))
                newToNameName = if null types && null pats then finalToNameName else mkName ("toName" ++ show index)
                prevToNameName = mkName ("toName" ++ (if index > 0 then show $ index-1 else ""))
                newVarName = mkName (nameBase varName ++ "'")
                xName = mkName "x"

            foilConNames :: Int -> [Type] -> [Pat] -> [Exp]
            foilConNames _ [] [] = []
            foilConNames index ((ConT tyName):types) ((VarP varName):pats)
              | tyName == patternT = VarE (mkName (nameBase varName ++ "'")) : foilConNames (index+1) types pats
              | tyName == nameT = VarE (mkName ("binder" ++ show index)) : foilConNames (index+1) types pats
              | otherwise = VarE varName : foilConNames (index+1) types pats


        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        countNames :: [Type] -> Int
        countNames [] = 0
        countNames ((ConT t):ts)
          | t == nameT = 1 + countNames ts
          | t == patternT = 1 + countNames ts
          | otherwise = countNames ts

    toMatchTerm :: Con -> Match
    toMatchTerm (NormalC conName params) =
      Match matchPat (matchBody conTypes matchPat) []

      where
        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName "scopedTerm"):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        matchBody :: [Type] -> Pat -> Body
        matchBody matchTypes (ConP name _ matchParams) =
          NormalB constr

          where
            constr = if checkPatScope matchTypes False
              then foldl AppE (VarE withPatternT) [VarE (mkName "toName"), VarE (mkName "scope"), VarE (fromJust (findPatternName matchTypes matchParams)), lamCase]
              else foldl AppE (ConE $ mkName ("Foil" ++ nameBase name)) (zipWith toExprWithoutScope matchTypes matchParams)
              where
                lamCase = LamE [VarP pat', VarP (mkName "toName'"), VarP (mkName "scope'")]
                  (foldl AppE (ConE (mkName ("Foil" ++ nameBase name))) (zipWith _toExpr matchTypes matchParams))

                pat' = mkName (nameBase (fromJust (findPatternName matchTypes matchParams)) ++ "'")

                findPatternName :: [Type] -> [Pat] -> Maybe Name
                findPatternName [] [] = Nothing
                findPatternName  ((ConT tyName):_) ((VarP varName):_)
                  | tyName == patternT = Just varName
                findPatternName (_:restT) (_:restP) = findPatternName restT restP

                _toExpr :: Type -> Pat -> Exp
                _toExpr (ConT tyName) (VarP patName)
                  | tyName == termT = foldl AppE (VarE toFoilTermT) [VarE (mkName "toName"), VarE (mkName "scope"), VarE patName]
                  | tyName == nameT = VarE patName
                  | tyName == patternT = VarE (mkName (nameBase patName ++ "'"))
                  | tyName == scopeT = foldl AppE (VarE toFoilScopedT) [VarE (mkName "toName'"), VarE (mkName "scope'"), VarE patName]
                  | otherwise = VarE patName

            checkPatScope :: [Type] -> Bool -> Bool
            checkPatScope [] _ = False
            checkPatScope ((ConT tyName):rest) patFound
              | tyName == patternT = checkPatScope rest True
              | tyName == scopeT && patFound = True
              | otherwise = checkPatScope rest patFound


            toExprWithoutScope :: Type -> Pat -> Exp
            toExprWithoutScope (ConT tyName) (VarP patName)
              | tyName == nameT = AppE (VarE $ mkName "toName") (VarE patName)
              | tyName == termT = AppE (AppE (AppE (VarE toFoilTermT) (VarE (mkName "toName"))) (VarE (mkName "scope"))) (VarE patName)
              | otherwise = VarE patName