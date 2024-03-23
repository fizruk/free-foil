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
  let toFoilPatternSignatures = map (toFoilPatternSigD n l . fst) splitedPatternCons
  let toFoilPatternFunctions = map toFoilPatternFunction splitedPatternCons

  return (
    toFoilPatternSignatures ++ 
    toFoilPatternFunctions ++
    [
    SigD toFoilScopedT (toFoilScopedSigType n)
    , FunD toFoilScopedT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilScopedBody []]

    , SigD withPatternT (withPatternSigType n l)
    , FunD withPatternT [Clause [VarP withPatternToNameArg, VarP withPatternScopeArg, VarP withPatternPatArg, VarP withPatternContArg] withPatternBody []]

    , SigD toFoilTermT (toFoilTermSigType n)
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

    withPatternToNameArg = mkName "toName"
    withPatternScopeArg = mkName "scope"
    withPatternPatArg = mkName "pat"
    withPatternContArg = mkName "cont"


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

    toFoilPatternFunction :: ([Type], [Con]) -> Dec
    toFoilPatternFunction (types, cons) =
      FunD toFoilPatternTLocal [Clause argumentPats toFoilPatternBodyLocal []]
        where 
          toFoilPatternTLocal = mkName (nameBase toFoilPatternT ++ typesNames)
          toFoilPatternBodyLocal = NormalB (LamCaseE (map toFoilPatternMatch cons))
          argumentPats = map VarP (toArgumentNames (1,1) types)

          typesNames = foldl (\str (ConT _typeName) -> str ++ getToFoilPatternSchemaLetter _typeName) "" types

          toArgumentNames :: (Integer, Integer) -> [Type] -> [Name]
          toArgumentNames (_, _) [] = []
          toArgumentNames (indxB, indxP) ((ConT _typeName):_types)
            | _typeName == nameT = mkName ("binder" ++ show indxB):toArgumentNames (indxB+1, indxP) _types
            | _typeName == patternT = mkName ("foilpat" ++ show indxP):toArgumentNames (indxB, indxP+1) _types
            | otherwise = toArgumentNames (indxB, indxP) _types
    
    toFoilPatternSigD :: Name -> Name -> [Type] -> Dec
    toFoilPatternSigD n l types = 
      SigD toFoilPatternTLocal (ForallT plainTVList []
        (foldr AppT
          (AppT (AppT ArrowT (ConT patternT)) returgingFoilPattern)  -- Pattern -> FoilPattern n l
          binderTypes -- NameBinder n l / FoilPattern n l
        ))
      where 
        returgingFoilPattern 
          | null binderTypes = foldl AppT (ConT foilPatternT) [VarT n, VarT n]
          | otherwise = foldl AppT (ConT foilPatternT) [VarT n, VarT l]
        plainTVList 
          | null binderTypes = [PlainTV n SpecifiedSpec]
          | otherwise = [PlainTV n SpecifiedSpec] ++ map (`PlainTV` SpecifiedSpec) interNames ++ [PlainTV l SpecifiedSpec]
        toFoilPatternTLocal = mkName (nameBase toFoilPatternT ++ typesNames)
        binderTypes = toArgumentTypes types (n : interNames) (interNames ++ [l])
        
        typesNames = foldl (\str (ConT _typeName) -> str ++ getToFoilPatternSchemaLetter _typeName) "" types
        interNames = generateTNames 1 (length types)

        toArgumentTypes :: [Type] -> [Name] -> [Name] -> [Type] 
        toArgumentTypes [] _ _ = []
        toArgumentTypes ((ConT _typeName):types_) (_n:restN) (_l:restL) 
          | _typeName == nameT = returningType ''Foil.NameBinder : toArgumentTypes types_ restN restL
          | _typeName == patternT = returningType foilPatternT : toArgumentTypes types_ restN restL
          | otherwise = toArgumentTypes types_ (_n:restN) (_l:restL)
          where
            returningType :: Name -> Type
            returningType _name = 
                AppT ArrowT (AppT (AppT (ConT _name) (VarT _n)) (VarT _l))
        
        generateTNames :: Int -> Int -> [Name]
        generateTNames from to
          | from >= to = []
          | otherwise = mkName ("t" ++ show from) : generateTNames (from + 1) to

    
    getToFoilPatternSchemaLetter :: Name -> String
    getToFoilPatternSchemaLetter _typeName 
        | _typeName == nameT = "B" 
        | _typeName == patternT = "P"
        | otherwise = "X"

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
          | tyName == nameT = WildP:toPats (n+1) types -- VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = WildP:toPats (n+1) types -- VarP (mkName $ "pat" ++ show n):toPats (n+1) types
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
            toExpr (ConT tyName) WildP indx
              | tyName == nameT = VarE (mkName ("binder" ++ show indx))
              | tyName == patternT = VarE (mkName ("foilpat" ++ show indx))
            toExpr (ConT _) (VarP patName) _ = VarE patName

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