{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.LambdaPi.Foil.TH.MkFoilData (mkFoilData) where

import Language.Haskell.TH

import qualified Language.LambdaPi.Foil as Foil


mkFoilData :: Name -> Name -> Name -> Name -> Q [Dec]
mkFoilData termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  let foilPatternConsNames = generateNames 1 (maximum (map getBindersNumber patternCons))
  let foilPatternPlainTvs = map (`PlainTV` ()) ([n] ++ foilPatternConsNames ++ [l])

  let foilPatternCons = map (toPatternCon n l) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (\cons -> toTermCon n l cons foilPatternConsNames) termCons

  return
    [ DataD [] foilTermT [PlainTV n ()] Nothing foilTermCons []
    , StandaloneDerivD Nothing [] (AppT (ConT ''Show) (AppT (ConT foilTermT) (VarT n)))
    , DataD [] foilScopeT [PlainTV n ()] Nothing foilScopeCons [DerivClause Nothing [ConT ''Show]]
    , DataD [] foilPatternT foilPatternPlainTvs Nothing foilPatternCons [DerivClause Nothing [ConT ''Show]]
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toPatternCon :: Name -> Name -> Con -> Con
    toPatternCon n l (NormalC conName  params) =
      NormalC foilConName (map toPatternParam paramsWithBinders)
      where
        paramsWithBinders = zip3 params (n : foilNames) (foilNames ++ [l])
        foilNames = generateNames 1 (getBinderNumber (map snd params) 0)
        
        foilConName = mkName ("Foil" ++ nameBase conName)
        toPatternParam ((_bang, ConT tyName), localN, localL)
          | tyName == nameT = (_bang, AppT (AppT (ConT ''Foil.NameBinder) (VarT localN)) (VarT localL))
        toPatternParam (_bangType, _, _) = _bangType

    getBindersNumber :: Con -> Int
    getBindersNumber (NormalC _ params) = getBinderNumber (map snd params) 0

    getBinderNumber :: [Type] -> Int -> Int
    getBinderNumber [] counter = counter
    getBinderNumber ((ConT tyName):types) counter
      | tyName == nameT = getBinderNumber types (counter + 1)
      | otherwise = getBinderNumber types counter

    generateNames :: Int -> Int -> [Name]
    generateNames from to
      | from >= to = []
      | otherwise = mkName ("t" ++ show from) : generateNames (from + 1) to

    toScopeCon :: Name -> Con -> Con
    toScopeCon n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (_bang, ConT tyName)
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toScopeParam _bangType = _bangType

    toTermCon :: Name -> Name -> Con -> [Name] -> Con
    toTermCon n l (NormalC conName params) foilPatternConsNames =
      GadtC [foilConName] (map toTermParam params) (AppT (ConT foilTermT) (VarT n))
      where
        foilNames = [n] ++ foilPatternConsNames ++ [l]
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, ConT tyName)
          | tyName == patternT = (_bang, foldl AppT (ConT foilPatternT) (map VarT foilNames))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toTermParam _bangType = _bangType