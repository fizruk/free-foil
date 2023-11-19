{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- Закомментировать
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

mkFoil :: Name -> Name -> Name -> Name -> Q [Dec]
mkFoil termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT
  let foilPatternCons = map (toPatternCon n l) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (toTermCon n l) termCons

  let toFoilTBody = NormalB (LamCaseE (map toMatchTerm termCons))
  return $
    [ DataD [] foilTermT [PlainTV n ()] Nothing foilTermCons []
    , StandaloneDerivD Nothing [] (AppT (ConT ''Show) (AppT (ConT foilTermT) (VarT n)))
    , DataD [] foilScopeT [PlainTV n ()] Nothing foilScopeCons [DerivClause Nothing [ConT ''Show]]
    , DataD [] foilPatternT [PlainTV n (), PlainTV l ()] Nothing foilPatternCons [DerivClause Nothing [ConT ''Show]]
    , FunD toFoilT [Clause [VarP (mkName "toName"), VarP (mkName "scope")] toFoilTBody []]
    -- , FunD fromFoilT []
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)
    toFoilT = mkName ("mktoFoil" ++ nameBase termT)
    fromFoilT = mkName ("fromFoil" ++ nameBase termT)

    toMatchTerm :: Con -> Match
    toMatchTerm (NormalC conName params) =
      Match matchPat (matchBody matchPat) []

      where 
        matchPat = ConP conName conTypes (toPats 0 conTypes)
        conTypes = map snd params

        toPats :: Int -> [Type] -> [Pat]
        toPats _ [] = []
        toPats n ((ConT tyName):types)
          | tyName == nameT = VarP (mkName $ "varName" ++ show n):toPats (n+1) types
          | tyName == patternT = VarP (mkName $ "pat" ++ show n):toPats (n+1) types
          | tyName == scopeT = VarP (mkName $ "scopedTerm" ++ show n):toPats (n+1) types
          | tyName == termT = VarP (mkName $ "term" ++ show n):toPats (n+1) types
          | otherwise = VarP (mkName ("x" ++ show n)):toPats (n+1) types
        
        matchBody :: Pat -> Body 
        matchBody (ConP name matchTypes matchParams) = 
          NormalB (foldr (\l r -> AppE r l) (ConE $ mkName ("Foil" ++ nameBase name)) (reverse (map toExpr (zip matchTypes matchParams))))

          where 
            toExpr :: (Type, Pat) -> Exp
            toExpr (ConT tyName, VarP patName)
              | tyName == nameT = AppE (VarE $ mkName "toName") (VarE patName)
              | tyName == patternT = VarE patName --Incorrect
              | tyName == scopeT = VarE patName --Incorrect
              | tyName == termT = AppE (AppE (AppE (VarE toFoilT) (VarE (mkName "toName"))) (VarE (mkName "scope"))) (VarE patName)
              | otherwise = VarE patName
            

    toPatternCon :: Name -> Name -> Con -> Con
    toPatternCon n l (NormalC conName params) =
      NormalC foilConName (map toPatternParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toPatternParam (bang, ConT tyName)
          | tyName == nameT = (bang, AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l))
        toPatternParam bangType = bangType

    toScopeCon :: Name -> Con -> Con
    toScopeCon n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (bang, ConT tyName)
          | tyName == termT = (bang, AppT (ConT foilTermT) (VarT n))
        toScopeParam bangType = bangType

    toTermCon :: Name -> Name -> Con -> Con
    toTermCon n l (NormalC conName params) =
      GadtC [foilConName] (map toTermParam params) (AppT (ConT foilTermT) (VarT n))
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (bang, ConT tyName)
          | tyName == patternT = (bang, AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l))
          | tyName == nameT = (bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (bang, AppT (ConT foilTermT) (VarT n))
        toTermParam bangType = bangType
