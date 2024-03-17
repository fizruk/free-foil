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

  let splitedPatternCons = getConsTypes patternCons []
  let toFoilPatternSignatures = map 
              (\(types, _) -> 
                let 
                  typesNames = foldl (\str (ConT _typeName) -> str ++ getToFoilPatternSchemaLetter _typeName
                                              ) "" types
                  toFoilPatternTLocal = mkName (nameBase toFoilPatternT ++ typesNames)
                  argumentTypesReversed = zipWith3 (\ (ConT _typeName) _n _l -> 
                                              if _typeName == nameT then AppT ArrowT (AppT (AppT (ConT ''Foil.NameBinder) (VarT _n)) (VarT _l))
                                              else if _typeName == patternT then AppT ArrowT (AppT (AppT (ConT foilPatternT) (VarT _n)) (VarT _l))
                                              else WildCardT) 
                                            types (mkName "n" : interNames) (interNames ++ [mkName "l"])
                  argumentTypes = filter (/= WildCardT) argumentTypesReversed
                  interNames = generateNames 1 (length types)
                  plainTVList = [PlainTV (mkName "n") SpecifiedSpec] ++ map (`PlainTV` SpecifiedSpec) interNames ++ [PlainTV (mkName "l") SpecifiedSpec]

                in if null argumentTypes
                  then 
                    SigD toFoilPatternTLocal (ForallT [PlainTV (mkName "n") SpecifiedSpec] []
                      (AppT (AppT ArrowT
                          (ConT patternT)) -- Pattern
                          (foldl AppT (ConT foilPatternT) [VarT (mkName "n"), VarT (mkName "n")]) -- FoilPattern n l
                      ))
                  else 
                    SigD toFoilPatternTLocal (ForallT plainTVList []
                      (foldr AppT
                        (AppT (AppT ArrowT
                          (ConT patternT)) -- Pattern
                          (foldl AppT (ConT foilPatternT) [VarT (mkName "n"), VarT (mkName "l")])) -- FoilPattern n l
                        argumentTypes -- NameBinder n l/FoilPattern n l
                      ))
              ) 
            splitedPatternCons
  let toFoilPatternFunctions = map 
              (\(types, cons) -> 
                let 
                  typesNames = foldl (\str (ConT _typeName) ->
                                              if _typeName == nameT then str ++ "B" 
                                              else if _typeName == patternT then str ++ "P"
                                              else str ++  "X") "" types
                  toFoilPatternTLocal = mkName (nameBase toFoilPatternT ++ typesNames)
                  (argumentNamesReversed, (_,_)) = foldl (\(args, (indxB, indxP)) (ConT _typeName) -> 
                                              if _typeName == nameT then (mkName ("binder" ++ show indxB):args, (indxB+1, indxP))
                                              else if _typeName == patternT then (mkName ("foilpat" ++ show indxP):args, (indxB, indxP+1))
                                              else (args, (indxB, indxP))) ([], (1::Integer,1::Integer)) types
                  argumentPats = map VarP (reverse argumentNamesReversed)
                  toFoilPatternBodyLocal = NormalB (LamCaseE (map toFoilPatternMatch cons))
                in FunD toFoilPatternTLocal [Clause argumentPats toFoilPatternBodyLocal []]
              ) 
            splitedPatternCons

  return (
    toFoilPatternSignatures ++ 
    toFoilPatternFunctions ++
    [
    SigD toFoilScopedT (ForallT [PlainTV n SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
    (AppT (AppT ArrowT
      (AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) -- (VarIdent -> Name n)
    (AppT (AppT ArrowT
      (ParensT (AppT (ConT (mkName "Scope")) (VarT n)))) -- Scope n
    (AppT (AppT ArrowT
       (ConT scopeT)) -- ScopedTerm
      (ParensT (AppT (ConT foilScopeT) (VarT n)))) -- FoilScopedTerm n
    )))
    , FunD toFoilScopedT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilScopedBody []]

    , SigD withPatternT (ForallT [PlainTV n SpecifiedSpec, PlainTV (mkName "r") SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
    (AppT (AppT ArrowT
      (AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) --(VarIdent -> Name n) 
    (AppT (AppT ArrowT
      (ParensT (AppT (ConT (mkName "Scope")) (VarT n)))) -- Scope n
    (AppT (AppT ArrowT
       (ConT patternT)) -- Pattern
    (AppT (AppT ArrowT
      (ForallT [PlainTV l SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT l)]  -- forall l. Distinct l
        (AppT (AppT ArrowT
          (ParensT (foldl AppT (ConT foilPatternT) [VarT n, VarT l]))) -- FoilPattern n l
        (AppT (AppT ArrowT
          (ParensT (AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT l))))) -- (VarIdent -> Name l)
        (AppT (AppT ArrowT
          (AppT (ConT (mkName "Scope")) (VarT l))) -- Scope l
          (VarT (mkName "r"))))))) -- r
      (VarT (mkName "r"))
    )))))
    , FunD withPatternT [Clause [VarP (mkName "toName"), VarP (mkName "scope"), VarP (mkName "pat"), VarP (mkName "cont")] withPatternBody []]


    , SigD toFoilTermT (ForallT [PlainTV n SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
    (AppT (AppT ArrowT
      (AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) -- (VarIdent -> Name n)
    (AppT (AppT ArrowT
      (ParensT (AppT (ConT (mkName "Scope")) (VarT n)))) -- Scope n
    (AppT (AppT ArrowT
       (ConT termT)) -- Term
      (ParensT (AppT (ConT foilTermT) (VarT n)))) -- FoilTerm n
    )))
    , FunD toFoilTermT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilTBody []]
    ])
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toFoilTermT = mkName ("toFoil" ++ nameBase termT)
    toFoilPatternT = mkName ("toFoil" ++ nameBase patternT)
    toFoilScopedT = mkName ("toFoil" ++ nameBase scopeT)
    withPatternT = mkName "withPattern"


    getToFoilPatternSchemaLetter :: Name -> String
    getToFoilPatternSchemaLetter _typeName 
        | _typeName == nameT = "B" 
        | _typeName == patternT = "P"
        | otherwise = "X"

    getConsTypes :: [Con] -> [([Type], [Con])] -> [([Type], [Con])]
    getConsTypes [] current = current
    getConsTypes ((NormalC conName params):cs) current = 
      getConsTypes cs newCurrent
      where 
        newCurrent = putIntoSplitedList conBinderNumber (NormalC conName params) current
        conBinderNumber = map snd params

    
    putIntoSplitedList :: [Type] -> Con -> [([Type], [Con])] -> [([Type], [Con])]
    putIntoSplitedList types con [] = [(types, [con])]
    putIntoSplitedList types con ((typesI, conList):rest) 
      | types == typesI = (typesI, con : conList):rest 
      | otherwise = (typesI, conList):putIntoSplitedList types con rest
    
    generateNames :: Int -> Int -> [Name]
    generateNames from to
      | from >= to = []
      | otherwise = mkName ("t" ++ show from) : generateNames (from + 1) to


    toFoilScopedMatch :: Con -> Match
    toFoilScopedMatch (NormalC conName params) =
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
          NormalB (foldl AppE (ConE $ mkName ("Foil" ++ nameBase name)) (zipWith toExpr matchTypes matchParams))

          where
            toExpr :: Type -> Pat -> Exp
            toExpr (ConT tyName) (VarP patName)
              | tyName == termT = AppE (AppE (AppE (VarE toFoilTermT) (VarE (mkName "toName"))) (VarE (mkName "scope"))) (VarE patName)
              | otherwise = VarE patName

    toFoilPatternMatch :: Con -> Match
    toFoilPatternMatch (NormalC conName params) =
      Match matchPat (matchBody conTypes matchPat) []

      where
        matchPat = ConP conName [] (toPats 1 conTypes)
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
        matchBody matchTypes (ConP name _ matchParams) = NormalB
          (foldl AppE (ConE (mkName ("Foil" ++ nameBase name)))
            (zipWith3 toExpr matchTypes matchParams argumentIndexes))

          where
            argumentIndexes = typesToIndexes matchTypes (1,1,1)
            
            toExpr :: Type -> Pat -> Int -> Exp
            toExpr (ConT tyName) (VarP patName) indx
              | tyName == nameT = VarE (mkName ("binder" ++ show indx))
              | tyName == patternT = VarE (mkName ("foilpat" ++ show indx))
              | otherwise = VarE patName

            typesToIndexes :: [Type] -> (Int,Int,Int) -> [Int]
            typesToIndexes [] _ = []
            typesToIndexes ((ConT tyName):ts) (bindI, pattI, restI)
              | tyName == nameT = bindI : typesToIndexes ts (bindI+1, pattI,restI)
              | tyName == patternT = pattI : typesToIndexes ts (bindI, pattI+1,restI)
              | otherwise = restI : typesToIndexes ts (bindI, pattI, restI+1)

    withPatternMatch :: Con -> Match
    withPatternMatch (NormalC conName params) =
      Match matchPat (matchBody conTypes matchPat) []
      where
        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params
        foilConstrName = mkName ("Foil" ++ nameBase conName)

        matchBody :: [Type] -> Pat -> Body
        matchBody matchTypes (ConP _ _ matchParams) = 
          NormalB (updateNameBinders 0 matchTypes matchParams)
          where 
            letPat = LetE [
              ValD (VarP (mkName "pat'")) (NormalB (foldl AppE (ConE foilConstrName) (foilConNames 0 matchTypes matchParams))) []
              ] applyConWithPat

            applyConWithPat 
              | countNames conTypes == 0 = foldl AppE (VarE (mkName "cont")) [VarE (mkName "pat'"), VarE (mkName "toName"), VarE (mkName "scope")]
              | otherwise = foldl AppE (VarE (mkName "cont")) [VarE (mkName "pat'"), VarE (mkName "toName'"), VarE (mkName "scope'")]
            
            foilConNames :: Int -> [Type] -> [Pat] -> [Exp]
            foilConNames _ [] [] = []
            foilConNames index ((ConT tyName):types) ((VarP varName):pats)
              | tyName == patternT = VarE (mkName (nameBase varName ++ "'")) : foilConNames (index+1) types pats
              | tyName == nameT = VarE (mkName ("binder" ++ show index)) : foilConNames (index+1) types pats
              | otherwise = VarE varName : foilConNames (index+1) types pats

            updateNameBinders :: Int -> [Type] -> [Pat] -> Exp
            updateNameBinders _ [] [] = letPat
            updateNameBinders index [ConT tyName] [VarP varName]
              | tyName == nameT = AppE (AppE (VarE 'Foil.withFresh) (VarE prevScopeName))
                (LamE [VarP newBinderName]
                    (LetE [
                      ValD (VarP newScopeName) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE newBinderName, VarE prevScopeName])) [],
                      FunD newToNameName
                        [Clause [VarP xName]
                          (GuardedB [
                            (NormalG (AppE (AppE (VarE (mkName "==")) (VarE xName)) (VarE (mkName ("varName" ++ show index)))), AppE (VarE (mkName "nameOf")) (VarE newBinderName)),
                            (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE prevToNameName) (VarE xName)))
                          ]) []]] (updateNameBinders (index+1) [] [])))
              | tyName == patternT = foldl AppE (VarE withPatternT) [VarE prevToNameName, VarE prevScopeName, VarE varName, 
                  LamE [VarP (mkName (nameBase varName ++ "'")), VarP newToNameName, VarP newScopeName] (updateNameBinders (index+1) [] [])
                ]
              | otherwise = updateNameBinders (index+1) [] []
              where
                newBinderName = mkName ("binder" ++ show index)
                newScopeName = mkName "scope'"
                prevScopeName = mkName ("scope" ++ (if index > 0 then show $ index-1 else ""))
                newToNameName = mkName "toName'"
                prevToNameName = mkName ("toName" ++ (if index > 0 then show $ index-1 else ""))
                xName = mkName "x"

            updateNameBinders index ((ConT tyName):types) ((VarP varName):pats)
              | tyName == nameT = AppE (AppE (VarE 'Foil.withFresh) (VarE prevScopeName))
                (LamE [VarP newBinderName]
                    (LetE [
                      ValD (VarP newScopeName) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE newBinderName, VarE prevScopeName])) [],
                      FunD newToNameName
                        [Clause [VarP xName]
                          (GuardedB [
                            (NormalG (AppE (AppE (VarE (mkName "==")) (VarE xName)) (VarE (mkName ("varName" ++ show index)))), AppE (VarE (mkName "nameOf")) (VarE newBinderName)),
                            (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE prevToNameName) (VarE xName)))
                          ]) []]
                    ] (updateNameBinders (index+1) types pats)))
              | tyName == patternT = foldl AppE (VarE withPatternT) [VarE prevToNameName, VarE prevScopeName, VarE varName, 
                  LamE [VarP (mkName (nameBase varName ++ "'")), VarP newToNameName, VarP newScopeName] (updateNameBinders (index+1) types pats)
                ]
              | otherwise = updateNameBinders (index+1) types pats
              where
                newBinderName = mkName ("binder" ++ show index)
                newScopeName = mkName ("scope" ++ show index)
                prevScopeName = mkName ("scope" ++ (if index > 0 then show $ index-1 else ""))
                newToNameName = mkName ("toName" ++ show index)
                prevToNameName = mkName ("toName" ++ (if index > 0 then show $ index-1 else ""))
                xName = mkName "x"


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