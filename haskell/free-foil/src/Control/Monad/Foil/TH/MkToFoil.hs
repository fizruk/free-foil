{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Control.Monad.Foil.TH.MkToFoil (mkToFoil) where

import           Language.Haskell.TH
import Language.Haskell.TH.Syntax (addModFinalizer)

import qualified Control.Monad.Foil  as Foil
import           Data.Maybe          (fromJust, catMaybes)

-- | Generate conversion functions from raw to scope-safe representation.
mkToFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkToFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  let toFoilTBody = NormalB (LamCaseE (map toMatchTerm termCons))
  -- let toFoilPatternBody = NormalB (LamCaseE (map toFoilPatternMatch patternCons))
  let toFoilScopedBody = NormalB (LamCaseE (map toFoilScopedMatch scopeCons))
  let withPatternBody = NormalB (CaseE (VarE (mkName "pat")) (map withPatternMatch patternCons))

  let toFoilPatternSignatures = toFoilPatternSignatureGenerator patternCons
  let splitedPatternCons = splitConsesByBinderNumber patternCons []
  let toFoilPatternFunctions = map
              (\((bindersNumber, patsNumber), cons) ->
                let
                  toFoilPatternTLocal = mkName (nameBase toFoilPatternT ++ show bindersNumber ++ show patsNumber)
                  varPBinders = map (\x -> VarP (mkName ("binder" ++ show x))) [1..bindersNumber]
                  varPPats = map (\x -> VarP (mkName ("foilpat" ++ show x))) [1..patsNumber]
                  toFoilPatternBodyLocal = NormalB (LamCaseE (map toFoilPatternMatch cons))
                in FunD toFoilPatternTLocal [Clause (varPBinders ++ varPPats) toFoilPatternBodyLocal []]
              )
            splitedPatternCons

  extendScopeFoilPattenD <- mkExtendScopeFoilPattern nameT patternT
  withRefreshedFoilPatternD <- mkWithRefreshedFoilPattern nameT patternT
  return (
    extendScopeFoilPattenD ++
    withRefreshedFoilPatternD ++
    -- toFoilPatternSignatures ++
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
          (ParensT (foldl AppT (ConT foilPatternT) ([VarT n, VarT l])))) -- FoilPattern n l
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

    splitConsesByBinderNumber :: [Con] -> [((Int, Int), [Con])] -> [((Int, Int), [Con])]
    splitConsesByBinderNumber [] current = current
    splitConsesByBinderNumber ((NormalC conName params):cs) current =
      splitConsesByBinderNumber cs newCurrent
      where
        newCurrent = putIntoSplitedList conBinderNumber (NormalC conName params) current
        conBinderNumber = getBinderPatNumber (map snd params) (0, 0)


    putIntoSplitedList :: (Int, Int) -> Con -> [((Int, Int), [Con])] -> [((Int, Int), [Con])]
    putIntoSplitedList n con [] = [(n, [con])]
    putIntoSplitedList (nBinder, nPat) con (((niBinder, niPat), conList):rest)
      | nBinder == niBinder && nPat == niPat = ((niBinder, niPat), con : conList):rest
      | otherwise = ((niBinder, niPat), conList):putIntoSplitedList (nBinder, nPat) con rest

    getBinderPatNumber :: [Type] -> (Int, Int) -> (Int, Int)
    getBinderPatNumber [] counter = counter
    getBinderPatNumber ((ConT tyName):types) (binderCounter, patCount)
      | tyName == nameT = getBinderPatNumber types (binderCounter+1, patCount)
      | tyName == patternT = getBinderPatNumber types (binderCounter, patCount+1)
      | otherwise = getBinderPatNumber types (binderCounter, patCount)

    getBinderNumber :: [Type] -> Int -> Int
    getBinderNumber [] counter = counter
    getBinderNumber ((ConT tyName):types) counter
      | tyName == nameT = getBinderNumber types counter+1
      | tyName == patternT = getBinderNumber types counter+1
      | otherwise = getBinderNumber types counter

    generateNames :: Int -> Int -> [Name]
    generateNames from to
      | from >= to = []
      | otherwise = mkName ("t" ++ show from) : generateNames (from + 1) to

    toFoilPatternSignatureGenerator :: [Con] -> [Dec]
    toFoilPatternSignatureGenerator cons =
       concatMap (`toFoilPatternSignatureN` cons) [0..maxBinderNumber]

      where
        maxBinderNumber :: Int
        maxBinderNumber = maximum (map
            (\case
                (NormalC _ params) -> (getBinderNumber (map snd params) 0)
                _ -> 0
            ) cons)

        toFoilPatternSignatureN :: Int -> [Con] -> [Dec]
        toFoilPatternSignatureN _ [] =  []
        toFoilPatternSignatureN bindersNumber ((NormalC _ params):cs)
          | bindersNumber == getBinderNumber (map snd params) 0 =
            if bindersNumber == 0
              then
                [SigD (mkName (nameBase toFoilPatternT ++ show bindersNumber)) (ForallT plainTVList []
                  (foldr AppT
                    (AppT (AppT ArrowT
                      (ConT patternT)) -- Pattern
                      (foldl AppT (ConT foilPatternT) [VarT (mkName "n"), VarT (mkName "n")])) -- FoilPattern n n
                    nameBindersList -- NameBinder n l
                  ))]
              else
                [SigD (mkName (nameBase toFoilPatternT ++ show bindersNumber)) (ForallT plainTVList []
                  (foldr AppT
                    (AppT (AppT ArrowT
                      (ConT patternT)) -- Pattern
                      (foldl AppT (ConT foilPatternT) [VarT (mkName "n"), VarT (mkName "l")])) -- FoilPattern n l
                    nameBindersList -- NameBinder n l
                  ))]
          | otherwise = toFoilPatternSignatureN bindersNumber cs
            where
              interNames = generateNames 1 bindersNumber
              maxInterNames = generateNames 1 maxBinderNumber
              -- varTList = [VarT (mkName "n")] ++ map VarT maxInterNames ++ [VarT (mkName "l")]
              plainTVList = [PlainTV (mkName "n") SpecifiedSpec] ++ map (`PlainTV` SpecifiedSpec) interNames ++ [PlainTV (mkName "l") SpecifiedSpec]
              nameBindersList =
                if bindersNumber == 0
                  then []
                  else zipWith (curry nameBinderGenerator) (mkName "n" : interNames)
                                                            (interNames ++ [mkName "l"])

              nameBinderGenerator :: (Name, Name) -> Type
              nameBinderGenerator (_n, _l) = AppT ArrowT
                (AppT (AppT (ConT ''Foil.NameBinder) (VarT _n)) (VarT _l))


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
            (zipWith3 toExpr matchTypes matchParams binderIndexes))

          where
            binderIndexes = typesToBinderIndexes matchTypes 1
            toExpr :: Type -> Pat -> Int -> Exp
            -- toExpr _ WildP = VarE (mkName "binder")
            toExpr (ConT tyName) (VarP patName) indx
              | tyName == nameT = VarE (mkName ("binder" ++ show indx))
              | tyName == patternT = VarE (mkName ("foilpat" ++ show indx))
              | otherwise = VarE patName

            typesToBinderIndexes :: [Type] -> Int -> [Int]
            typesToBinderIndexes [] _ = []
            typesToBinderIndexes ((ConT tyName):ts) n
              | tyName == nameT = n : typesToBinderIndexes ts (n+1)
              | otherwise = n : typesToBinderIndexes ts n

    withPatternMatch :: Con -> Match
    withPatternMatch (NormalC conName params) =
      Match matchPat (matchBody conTypes matchPat) []

      where
        matchBody :: [Type] -> Pat -> Body
        matchBody matchTypes (ConP name _ matchParams) =
          NormalB (updateNameBinders 0 matchTypes matchParams letPat)
          where
            letPat = LetE [
              ValD (VarP (mkName "pat'")) (NormalB (foldl AppE (ConE (mkName ("Foil" ++ nameBase conName))) (foilConNames 0 matchTypes matchParams))) []
              ] applyConWithPat
            applyConWithPat
              | countNames conTypes == 0 = foldl AppE (VarE (mkName "cont")) [VarE (mkName "pat'"), VarE (mkName "toName"), VarE (mkName "scope")]
              | otherwise = foldl AppE (VarE (mkName "cont")) [VarE (mkName "pat'"), VarE (mkName "toName'"), VarE (mkName "scope'")]

            foilConNames :: Int -> [Type] -> [Pat] -> [Exp]
            foilConNames index [] [] = []
            foilConNames index ((ConT tyName):types) ((VarP varName):pats)
              | tyName == patternT = (VarE $ mkName (nameBase varName ++ "'")) : foilConNames (index+1) types pats
              | tyName == nameT = (VarE (mkName ("binder" ++ show index))) : foilConNames (index+1) types pats
              | otherwise = (VarE varName) : foilConNames (index+1) types pats

            updateNameBinders :: Int -> [Type] -> [Pat] -> Exp -> Exp
            updateNameBinders index [] [] letPat = letPat
            updateNameBinders index ((ConT tyName):[]) ((VarP varName):[]) letPat
              | tyName == nameT = AppE (AppE (VarE 'Foil.withFresh) (VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else "")))))
                (LamE [VarP (mkName ("binder" ++ show index))]
                    (LetE [
                      ValD (VarP (mkName "scope'")) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE (mkName ("binder" ++ show index)), VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else "")))])) [],
                      FunD (mkName "toName'")
                        [Clause [VarP (mkName "x")]
                          (GuardedB [
                            (NormalG (AppE (AppE (VarE (mkName "==")) (VarE (mkName "x"))) (VarE (mkName ("varName" ++ show index)))), AppE (VarE (mkName "nameOf")) (VarE (mkName ("binder" ++ show index)))),
                            (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE (mkName ("toName" ++ (if index > 0 then show $ index-1 else "")))) (VarE (mkName "x"))))
                          ]) []]] (updateNameBinders (index+1) [] [] letPat)))
              | tyName == patternT = foldl AppE (VarE withPatternT) [VarE (mkName ("toName" ++ (if index > 0 then show $ index-1 else ""))), VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else ""))), VarE varName,
                  (LamE [VarP (mkName (nameBase varName ++ "'")), VarP (mkName "toName'"), VarP (mkName "scope'")] (updateNameBinders (index+1) [] [] letPat))
                ]
              | otherwise = updateNameBinders (index+1) [] [] letPat
            updateNameBinders index ((ConT tyName):types) ((VarP varName):pats) letPat
              | tyName == nameT = AppE (AppE (VarE 'Foil.withFresh) (VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else "")))))
                (LamE [VarP (mkName ("binder" ++ show index))]
                  (LetE [
                      ValD (VarP (mkName ("scope" ++ show index))) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE (mkName ("binder" ++ show index)), VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else "")))])) [],
                      FunD (mkName ("toName" ++ show index))
                        [Clause [VarP (mkName "x")]
                          (GuardedB [
                            (NormalG (AppE (AppE (VarE (mkName "==")) (VarE (mkName "x"))) (VarE (mkName ("varName" ++ show index)))), AppE (VarE (mkName "nameOf")) (VarE (mkName ("binder" ++ show index)))),
                            (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE (mkName ("toName" ++ (if index > 0 then show $ index-1 else "")))) (VarE (mkName "x"))))
                          ]) []]
                    ] (updateNameBinders (index+1) types pats letPat)))
              | tyName == patternT = foldl AppE (VarE withPatternT) [VarE (mkName ("toName" ++ (if index > 0 then show $ index-1 else ""))), VarE (mkName ("scope" ++ (if index > 0 then show $ index-1 else ""))), VarE varName,
                  (LamE [VarP (mkName (nameBase varName ++ "'")), VarP (mkName ("toName" ++ show index)), VarP (mkName ("scope" ++ show index))] (updateNameBinders (index+1) types pats letPat))
                ]
              | otherwise = updateNameBinders (index+1) types pats letPat


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
              then toExprScopeExt
              else foldl AppE (ConE $ mkName ("Foil" ++ nameBase name)) (zipWith toExprWithoutScope matchTypes matchParams)


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

            toExprScopeExt = foldl AppE (VarE withPatternT) [VarE (mkName "toName"), VarE (mkName "scope"), VarE (fromJust (findPatternName matchTypes matchParams)), lamCase]
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

-- | Generate a function to extend scope with variables from a given pattern.
mkExtendScopeFoilPattern
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkExtendScopeFoilPattern nameT patternT = do
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT

  extendScopePatternSignature <-
    SigD extendScopePatternFunName <$>
      [t| forall n l. $(return (ConT foilPatternT)) n l -> Foil.Scope n -> Foil.Scope l |]

  composefun <- [e| (.) |]
  idfun <- [e| id |]
  extendScopeFun <- [e| Foil.extendScope |]

  addModFinalizer $ putDoc (DeclDoc extendScopePatternFunName)
    "Extend a scope with the names bound by the given pattern.\nThis is a more flexible version of 'Control.Monad.Foil.extendScope'."

  return
    [ extendScopePatternSignature
    , extendScopePatternBody extendScopeFun composefun idfun patternCons
    ]
  where
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    toFoilPatternT = mkName ("toFoil" ++ nameBase patternT)

    extendScopePatternFunName = mkName ("extendScopeFoil" ++ nameBase patternT)
    extendScopePatternBody extendScopeFun composefun idfun patternCons = FunD extendScopePatternFunName
      [Clause [VarP p] (NormalB (CaseE (VarE p) (map toMatch patternCons))) []]
      where
        p = mkName "pattern"
        toMatch (NormalC conName conParams) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            foilConName = mkName ("Foil" ++ nameBase conName)
            conParamPatterns = map toConParamPattern conParamVars
            conMatchExts = map snd (catMaybes conParamVars)
            conMatchBody = foldr (\f g -> InfixE (Just g) composefun (Just f)) idfun conMatchExts

            toConParamPattern Nothing = WildP
            toConParamPattern (Just (x, _f)) = VarP x

            conParamVars = zipWith mkConParamVar conParams [1..]

            mkConParamVar :: BangType -> Int -> Maybe (Name, Exp)
            mkConParamVar (_bang, ConT tyName) i
              | tyName == nameT    = Just (x, AppE extendScopeFun (VarE x))
              | tyName == patternT = Just (x, AppE (VarE extendScopePatternFunName) (VarE x))
              where
                x = mkName ("x" <> show i)
            mkConParamVar (_bang, _type) _i = Nothing

-- | Generate a function to extend scope with variables from a given pattern.
mkWithRefreshedFoilPattern
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkWithRefreshedFoilPattern nameT patternT = do
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT

  withRefreshedFoilPatternSignature <-
    SigD withRefreshedFoilPatternFunName <$>
      [t| forall o e n l r.
            ( Foil.Distinct o, Foil.InjectName e, Foil.Sinkable e )
            => Foil.Scope o
            -> $(return (ConT foilPatternT)) n l
            -> (forall o'. Foil.DExt o o'
                  => (Foil.Substitution e n o -> Foil.Substitution e l o')
                  -> $(return (ConT foilPatternT)) o o'
                  -> r)
            -> r
        |]

  composefun <- [e| (.) |]
  addRenameFun <- [e| Foil.addRename |]
  nameOfFun <- [e| Foil.nameOf |]
  sinkFun <- [e| Foil.sink |]
  withRefreshedFun <- [e| Foil.withRefreshed |]
  extendScopeFun <- [e| Foil.extendScope |]

  addModFinalizer $ putDoc (DeclDoc withRefreshedFoilPatternFunName)
    "Refresh (if needed) bound variables introduced in a pattern.\nThis is a more flexible version of 'Control.Monad.Foil.withRefreshed'."

  return
    [ withRefreshedFoilPatternSignature
    , withRefreshedFoilPatternBody composefun addRenameFun nameOfFun sinkFun withRefreshedFun extendScopeFun patternCons
    ]
  where
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    toFoilPatternT = mkName ("toFoil" ++ nameBase patternT)

    extendScopePatternFunName = mkName ("extendScopeFoil" ++ nameBase patternT)
    extendScopePatternFun = VarE extendScopePatternFunName

    withRefreshedFoilPatternFunName = mkName ("withRefreshedFoil" ++ nameBase patternT)
    withRefreshedFoilPatternFun = VarE withRefreshedFoilPatternFunName

    withRefreshedFoilPatternBody composefun addRenameFun nameOfFun sinkFun withRefreshedFun extendScopeFun patternCons = FunD withRefreshedFoilPatternFunName
      [Clause [VarP scope, VarP pattern, VarP cont] (NormalB (CaseE (VarE pattern) (map toMatch patternCons))) []]
      where
        scope = mkName "scope"
        pattern = mkName "pattern"
        cont = mkName "cont"

        toMatch (NormalC conName conParams) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE scope) sinkFun (ConE foilConName) conParams

            go i scope' f p [] = AppE (AppE (VarE cont) f) p
            go i scope' f p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  AppE
                    (AppE (AppE withRefreshedFun scope') (AppE nameOfFun (VarE xi)))
                    (LamE [VarP xi']
                      (LetE [ValD (VarP scopei) (NormalB (AppE (AppE extendScopeFun (VarE xi')) scope')) []]
                        (go (i+1) (VarE scopei) (InfixE (Just fi) composefun (Just f)) (AppE p (VarE xi')) conParams)))
              | tyName == patternT =
                  AppE
                    (AppE (AppE withRefreshedFoilPatternFun scope') (VarE xi))
                    (LamE [VarP xsubst, VarP xi']
                      (LetE [ValD (VarP scopei) (NormalB (AppE (AppE extendScopePatternFun (VarE xi')) scope')) []]
                        (go (i+1) (VarE scopei) (InfixE (Just (VarE xsubst)) composefun (Just f)) (AppE p (VarE xi')) conParams)))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                scopei = mkName ("scope" <> show i)
                xsubst = mkName ("subst" <> show i)
                subst = mkName "subst"
                fi = LamE [VarP subst]
                      (AppE (AppE (AppE addRenameFun
                        (VarE subst))
                        (VarE xi))
                        (AppE nameOfFun (VarE xi')))

            foilConName = mkName ("Foil" ++ nameBase conName)
            conParamPatterns = map toConParamPattern conParamVars
            conMatchExts = map snd (catMaybes conParamVars)

            toConParamPattern Nothing = WildP
            toConParamPattern (Just (x, _f)) = VarP x

            conParamVars = zipWith mkConParamVar conParams [1..]

            mkConParamVar :: BangType -> Int -> Maybe (Name, Exp)
            mkConParamVar (_bang, ConT tyName) i
              | tyName == nameT    = Just (x, AppE extendScopeFun (VarE x))
              | tyName == patternT = Just (x, AppE (VarE extendScopePatternFunName) (VarE x))
              where
                x = mkName ("x" <> show i)
            mkConParamVar (_bang, _type) _i = Nothing
