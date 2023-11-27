{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Закомментировать
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-} -- Закомментировать
module Language.LambdaPi.Foil.TH where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil

-- Foil

-- data FoilTerm n where
--   FoilVar :: Foil.Name n -> FoilTerm n
--   FoilApp :: FoilTerm n -> FoilTerm n -> FoilTerm n
--   FoilLam :: FoilPattern n l -> FoilTerm l -> FoilTerm n

-- data FoilPattern n l where
--   FoilPatternVar :: Foil.NameBinder n l -> FoilPattern n l

-- data FoilScopedTerm n where
--   FoilScopedTerm :: FoilTerm n -> FoilScopedTerm n

mkFoilData :: Name -> Name -> Name -> Name -> Q [Dec]
mkFoilData termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT
  let foilPatternCons = map (toPatternCon n l) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (toTermCon n l) termCons

  return 
    [ DataD [] foilTermT [PlainTV n ()] Nothing foilTermCons []
    , StandaloneDerivD Nothing [] (AppT (ConT ''Show) (AppT (ConT foilTermT) (VarT n)))
    , DataD [] foilScopeT [PlainTV n ()] Nothing foilScopeCons [DerivClause Nothing [ConT ''Show]]
    , DataD [] foilPatternT [PlainTV n (), PlainTV l ()] Nothing foilPatternCons [DerivClause Nothing [ConT ''Show]]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toPatternCon :: Name -> Name -> Con -> Con
    toPatternCon n l (NormalC conName  params) =
      NormalC foilConName (map toPatternParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toPatternParam (_bang, ConT tyName)
          | tyName == nameT = (_bang, AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l))
        toPatternParam _bangType = _bangType

    toScopeCon :: Name -> Con -> Con
    toScopeCon n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (_bang, ConT tyName)
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toScopeParam _bangType = _bangType

    toTermCon :: Name -> Name -> Con -> Con
    toTermCon n l (NormalC conName params) =
      GadtC [foilConName] (map toTermParam params) (AppT (ConT foilTermT) (VarT n))
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, ConT tyName)
          | tyName == patternT = (_bang, AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toTermParam _bangType = _bangType


mkToFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkToFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  let toFoilTBody = NormalB (LamCaseE (map toMatchTerm termCons))
  let toFoilPatternBody = NormalB (LamCaseE (map toFoilPatternMatch patternCons))
  let toFoilScopedBody = NormalB (LamCaseE (map toFoilScopedMatch scopeCons))
  let withPatternBody = NormalB (CaseE (VarE (mkName "pat")) (map withPatternMatch patternCons))

  return [
    SigD toFoilPatternT (ForallT [PlainTV n SpecifiedSpec, PlainTV l SpecifiedSpec] []
    (AppT (AppT ArrowT 
      ( AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l))) -- NameBinder n l
    (AppT (AppT ArrowT 
      (ConT patternT)) -- Pattern
      (AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))) -- FoilScopedTerm n
    ))
    , FunD toFoilPatternT [Clause [VarP (mkName "binder")] toFoilPatternBody []]
    
    , SigD toFoilScopedT (ForallT [PlainTV n SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
    (AppT (AppT ArrowT 
      ( AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) -- (VarIdent -> Name n)
    (AppT (AppT ArrowT 
      (ParensT (AppT (ConT (mkName "Scope")) (VarT n)))) -- Scope n
    (AppT (AppT ArrowT 
       (ConT scopeT)) -- ScopedTerm
      (ParensT (AppT (ConT foilScopeT) (VarT n)))) -- FoilScopedTerm n
    )))
    , FunD toFoilScopedT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilScopedBody []]
    
    , SigD withPatternT (ForallT [PlainTV n SpecifiedSpec, PlainTV (mkName "r") SpecifiedSpec] [AppT (ConT (mkName "Distinct")) (VarT n)]
    (AppT (AppT ArrowT 
      ( AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) --(VarIdent -> Name n) 
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
      ( AppT (AppT ArrowT (ConT nameT)) (AppT (ConT ''Foil.Name) (VarT n)))) -- (VarIdent -> Name n)
    (AppT (AppT ArrowT 
      (ParensT (AppT (ConT (mkName "Scope")) (VarT n)))) -- Scope n
    (AppT (AppT ArrowT 
       (ConT termT)) -- Term
      (ParensT (AppT (ConT foilTermT) (VarT n)))) -- FoilTerm n
    )))
    , FunD toFoilTermT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilTBody []]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    
    toFoilTermT = mkName ("toFoil" ++ nameBase termT)
    toFoilPatternT = mkName ("toFoil" ++ nameBase patternT)
    toFoilScopedT = mkName ("toFoil" ++ nameBase scopeT)
    withPatternT = mkName "withPattern"

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
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
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
        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types -- change to WildP
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Pat -> Body 
        matchBody matchTypes (ConP name _ matchParams) = NormalB
          (foldl AppE (ConE (mkName ("Foil" ++ nameBase name)))
            (zipWith toExpr matchTypes matchParams))

          where 
            toExpr :: Type -> Pat -> Exp
            -- toExpr _ WildP = VarE (mkName "binder")
            toExpr (ConT tyName) (VarP patName)
              | tyName == nameT = VarE (mkName "binder")
              | otherwise = VarE patName

    withPatternMatch :: Con -> Match
    withPatternMatch (NormalC conName params) = 
      Match matchPat (NormalB body) []

      where 
        body
         | ifContainTerm conTypes = AppE (AppE (VarE 'Foil.withFresh) (VarE (mkName "scope"))) withFreshLamPat
         | otherwise = LetE [decl] (AppE (AppE (AppE (VarE (mkName "cont")) (VarE (mkName "pat'"))) (VarE (mkName "toName"))) (VarE (mkName "scope")))
            where
              decl = ValD (VarP (mkName "pat'")) (NormalB (foldl AppE (ConE (mkName ("Foil" ++ nameBase conName))) ((\ (ConP _ _ conParams) -> map (\(VarP x) -> VarE x) conParams) matchPat)))[]

              withFreshLamPat = LamE [VarP (mkName "binder")] 
                  (LetE [
                    ValD (VarP (mkName "scope'")) (NormalB (foldl AppE (VarE 'Foil.extendScope) [VarE (mkName "binder"), VarE (mkName "scope")])) [],
                    FunD (mkName "toName'") 
                      [Clause [VarP (mkName "x")] 
                        (GuardedB [
                          (NormalG (AppE (AppE (VarE (mkName "==")) (VarE (mkName "x"))) (VarE (mkName "varName0"))), AppE (VarE (mkName "nameOf")) (VarE (mkName "binder"))),
                          (NormalG (VarE (mkName "otherwise")), AppE (VarE 'Foil.sink) (AppE (VarE (mkName "toName")) (VarE (mkName "x"))))
                        ]) []],
                    ValD (VarP (mkName "pat'")) (NormalB (foldl AppE (VarE toFoilPatternT) [VarE (mkName "binder"), VarE (mkName "pat")])) [] 
                  ] 
                    (AppE (AppE (AppE (VarE (mkName "cont")) (VarE (mkName "pat'"))) (VarE (mkName "toName'"))) (VarE (mkName "scope'"))))

        matchPat = ConP conName [] (toPats 0 conTypes)
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

        ifContainTerm :: [Type] -> Bool
        ifContainTerm [] = False
        ifContainTerm ((ConT t):ts)
          | t == nameT = True
          | otherwise = ifContainTerm ts

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
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
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
            
            toExprScopeExt = foldl AppE (VarE withPatternT) [VarE (mkName "toName"), VarE (mkName "scope"), VarE (mkName "pat0"), lamCase]
              where 
                lamCase = LamE [VarP (mkName "pat'"), VarP (mkName "toName'"), VarP (mkName "scope'")] 
                  (foldl AppE (ConE (mkName ("Foil" ++ nameBase name))) [VarE (mkName "pat'"), foldl AppE (VarE toFoilScopedT) [VarE (mkName "toName'"), VarE (mkName "scope'"), VarE (mkName "scopedTerm1")]])


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
      ( AppT (ConT foilTermT) (VarT n))) -- FoilTerm n 
      (ConT termT)) -- Term
    )
    , FunD fromFoilTermT [Clause [] fromFoilTBody []]
    
    , SigD fromFoilPatternT (ForallT [PlainTV n SpecifiedSpec, PlainTV l SpecifiedSpec] []
    (AppT (AppT ArrowT 
      ( AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))) -- FoilPattern n l
      (ConT patternT)) -- Pattern
    )
    , FunD fromFoilPatternT [Clause [] fromFoilPatternBody []]
    
    , SigD fromFoilScopedTermT (ForallT [PlainTV n SpecifiedSpec] []
    (AppT (AppT ArrowT 
      ( AppT (ConT foilScopeT) (VarT n))) -- FoilScopedTerm n 
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

    fromMatchFoilPattern :: Con -> Match 
    fromMatchFoilPattern (NormalC conName params) = 
      Match matchPat (matchBody conTypes matchPat conName) []

      where 
        matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = ConP (mkName "UnsafeNameBinder") [] [VarP (mkName $ "binder" ++ show n)]:toPats (n+1) types -- change to WildP
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Pat -> Name -> Body 
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

          where 
            toExpr :: Type -> Pat -> Exp
            toExpr _ (ConP _ _ [VarP varName]) = AppE (ConE (mkName (nameBase nameT))) (AppE (VarE 'Foil.ppName) (VarE varName)) -- Уязвимость: mkName (nameBase nameT) предполагает что имя конструктора совпадает с именем типа. Но нет возможности выбрать подходищай конструктор так как непонятно как паттернматчить аргумент конструктора с нужным
            toExpr (ConT _) (VarP patName) = VarE patName
    
    fromMatchFoilScoped :: Con -> Match
    fromMatchFoilScoped (NormalC conName params) = 
      Match matchPat (matchBody conTypes matchPat conName) []

      where 
        matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
        conTypes = map snd params


        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName ("varName" ++ show n)):toPats (n+1) types -- change to WildP
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Pat -> Name -> Body 
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

          where 
            toExpr :: Type -> Pat -> Exp
            toExpr (ConT tyName) (VarP patName) 
              | tyName == termT = AppE (VarE fromFoilTermT) (VarE patName)
              | otherwise = VarE patName

    fromMatchFoilTerm :: Con -> Match
    fromMatchFoilTerm (NormalC conName params) = 
      Match matchPat (matchBody conTypes matchPat conName) []

      where 
        matchPat = ConP (mkName ("Foil" ++ nameBase conName)) [] (toPats 0 conTypes)
        conTypes = map snd params


        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName ("varName" ++ show n)):toPats (n+1) types -- change to WildP
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Pat -> Name -> Body 
        matchBody matchTypes (ConP _ _ matchParams) name = NormalB
          (foldl AppE (ConE name) (zipWith toExpr matchTypes matchParams))

          where 
            toExpr :: Type -> Pat -> Exp
            toExpr (ConT tyName) (VarP patName) 
              | tyName == nameT = AppE (ConE (mkName (nameBase nameT))) (AppE (VarE 'Foil.ppName) (VarE patName))
              | tyName == patternT = AppE (VarE fromFoilPatternT) (VarE patName)
              | tyName == scopeT =AppE (VarE fromFoilScopedTermT) (VarE patName)
              | tyName == termT = AppE (VarE fromFoilTermT) (VarE patName)
              | otherwise = VarE patName

mkInstancesFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkInstancesFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT
  let foilPatternCons = map (toPatternCon n l) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (toTermCon n l) termCons

  return [
      InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (ConT foilScopeT)) 
      [FunD (mkName "sinkabilityProof") (map clauseScopedTerm foilScopeCons)]
    , InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (AppT (ConT foilPatternT) (VarT n)))
      [FunD (mkName "sinkabilityProof") (map clausePattern foilPatternCons)]
    -- , InstanceD Nothing [] (AppT (ConT (mkName "Sinkable")) (ConT foilTermT))
    --   [FunD (mkName "sinkabilityProof") (map (\x -> clauseTerm x patternCons scopeCons) foilTermCons)]
    ]

  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    clauseScopedTerm :: Con -> Clause
    clauseScopedTerm (NormalC conName params) = 
      Clause [VarP (mkName "f"), ConP conName [] conPats] 
        (matchBody conTypes conName conPats)
      []

      where 
        conPats = toPats 0 conTypes
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((AppT (ConT tyName) _):types)
          | tyName == ''Foil.Name = VarP (mkName ("varName" ++ show n)):toPats (n+1) types 
          | tyName == foilPatternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == foilScopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == foilTermT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Name -> [Pat] -> Body 
        matchBody matchTypes name _conPats = NormalB 
          (foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats)) 

          where 
            toExpr :: Type -> Pat -> Exp
            toExpr ((AppT (ConT tyName) _)) (VarP patName) 
              | tyName == ''Foil.Name = AppE (VarE (mkName "f")) (VarE patName)
              | tyName == foilTermT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f"))) (VarE patName)
              | otherwise = VarE patName
    
    clausePattern :: Con -> Clause
    clausePattern (NormalC conName params) =
      Clause [VarP (mkName "f"), ConP conName [] conPats] 
        (matchBody conTypes conName conPats)
      []

      where 
        conPats = toPats 0 conTypes
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT simple):types) = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        toPats n ((AppT (AppT (ConT var) (VarT _)) (VarT _)):types)
          | var == ''Foil.NameBinder = ConP 'Foil.UnsafeNameBinder [] [VarP (mkName ("var" ++ show n))]:toPats (n+1) types 
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: [Type] -> Name -> [Pat] -> Body 
        matchBody matchTypes name _conPats = NormalB 
          (foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats)) 

          where 
            toExpr :: Type -> Pat -> Exp
            toExpr ((AppT (AppT (ConT var) (VarT _)) (VarT _))) (ConP unsafeBinder [] [VarP singleVar]) 
              | var == ''Foil.NameBinder = AppE (ConE 'Foil.UnsafeNameBinder) (AppE (VarE (mkName "f")) (VarE singleVar))
            toExpr _ (VarP patName) = VarE patName

    -- clauseTerm :: Con -> [Con] -> [Con] -> Clause
    -- clauseTerm (NormalC conNameTerm paramsTerm) consPattern consScoped =   
    --   Clause [VarP (mkName "f"), ConP conNameTerm [] conPats] 
    --     (matchBody conTypes conNameTerm conPats)
    --   []

    --   where 
    --     conPats = toPats 0 conTypes
    --     conTypes = map snd paramsTerm

    --     toPats :: Int -> [Type] -> [Pat]
    --     toPats _ [] = []
    --     toPats n (AppT (AppT (ConT fPT) (VarT _)) (VarT _):types) 
    --       | fPT == foilPatternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types  
    --     toPats n ((AppT (ConT _conName) (VarT _)):types)
    --       | _conName == ''Foil.Name = VarP (mkName ("varName" ++ show n)):toPats (n+1) types 
    --       | _conName == foilTermT = VarP (mkName $ "term" ++ show n):toPats (n+1) types 
    --       | _conName == foilScopeT = ConP foilScopeT [] [VarP (mkName $ "body" ++ show n)]:toPats (n+1) types -- Плохо что используется foilSopeT
    --       | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types

    --     matchBody :: [Type] -> Name -> [Pat] -> Body 
    --     matchBody matchTypes name _conPats = NormalB constr

    --       where 
    --         constr = if checkPatScope matchTypes False
    --           then sinkProofPatScope
    --           else foldl AppE (ConE name) (zipWith toExpr matchTypes _conPats)


    --         checkPatScope :: [Type] -> Bool -> Bool
    --         checkPatScope [] _ = False
    --         checkPatScope (AppT (AppT (ConT fPT) (VarT _)) (VarT _):rest) patFound
    --           | fPT == foilPatternT = checkPatScope rest True
    --           | otherwise = checkPatScope rest patFound
    --         checkPatScope ((AppT (ConT _conName) (VarT _)):rest) patFound
    --           | _conName == foilScopeT && patFound = True
    --           | otherwise = checkPatScope rest patFound

    --         toExpr :: Type -> Pat -> Exp
    --         toExpr ((AppT (ConT _conName) (VarT _))) (VarP varName) 
    --           | _conName == ''Foil.Name = AppE (VarE (mkName "f")) (VarE varName)
    --           | _conName == foilTermT = AppE (AppE (VarE (mkName "sinkabilityProof")) (VarE (mkName "f"))) (VarE varName)
    --           | otherwise = VarE varName
    --         toExpr _ (VarP patName) = VarE patName

    --         sinkProofPatScope = LamCaseE (map sinkPatMathc consPattern)
    --           where
    --             sinkPatMathc :: Con -> Match
    --             sinkPatMathc (NormalC conName paramsSinkPat) = 
    --               Match (ConP conName [] conPatsSinkPat) sinkPatBody []
                
    --               where 
    --                 sinkPatBody = 
    --                   if checkSinkNameBinder conTypesSinkPat
    --                     then VarE (mkName "f")
    --                     else AppE (ConE conNameTerm) (AppE (ConE conName))

    --                 toExprSinkPat :: Type -> Pat -> Exp
    --                 toExprSinkPat (AppT (AppT (ConT fPT) (VarT _)) (VarT _)) _ 
    --                   | fPT == foilPatternT = 

    --                 conPatsSinkPat = toPatsSinkPat 0 conTypesSinkPat
    --                 conTypesSinkPat = map snd paramsSinkPat

    --                 checkSinkNameBinder :: [Type] -> Bool
    --                 checkSinkNameBinder [] = False
    --                 checkSinkNameBinder (AppT (AppT (ConT fPT) (VarT _)) (VarT _):types) 
    --                   | fPT == ''Foil.NameBinder = True  
    --                 checkSinkNameBinder (_:types) = checkSinkNameBinder types

    --                 toPatsSinkPat :: Int -> [Type] -> [Pat]
    --                 toPatsSinkPat _ [] = []
    --                 toPatsSinkPat n (AppT (AppT (ConT fPT) (VarT _)) (VarT _):types) 
    --                   | fPT == ''Foil.NameBinder = VarP (mkName $ "binder" ++ show n):toPats (n+1) types  
    --                 toPatsSinkPat n (_:types) = VarP (mkName ("x" ++ show n)):toPats (n+1) types


    toPatternCon :: Name -> Name -> Con -> Con
    toPatternCon n l (NormalC conName  params) =
      NormalC foilConName (map toPatternParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toPatternParam (_bang, ConT tyName)
          | tyName == nameT = (_bang, AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l))
        toPatternParam _bangType = _bangType

    toScopeCon :: Name -> Con -> Con
    toScopeCon n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (_bang, ConT tyName)
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toScopeParam _bangType = _bangType

    toTermCon :: Name -> Name -> Con -> Con
    toTermCon n l (NormalC conName params) =
      GadtC [foilConName] (map toTermParam params) (AppT (ConT foilTermT) (VarT n))
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, ConT tyName)
          | tyName == patternT = (_bang, AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toTermParam _bangType = _bangType