{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Control.Monad.Foil.TH.MkFoilData (mkFoilData) where

import           Language.Haskell.TH

import qualified Control.Monad.Foil.Internal as Foil

-- FoilPatternPair :: forall l1. FoilPattern n l1 -> FoilPattern l1 l -> FoilPattern n l


mkFoilData :: Name -> Name -> Name -> Name -> Q [Dec]
mkFoilData termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  foilPatternCons <- mapM (toPatternCon n) patternCons
  let foilScopeCons = map (toScopeCon n) scopeCons
  let foilTermCons = map (toTermCon n l) termCons

  return
    [ DataD [] foilTermT [PlainTV n ()] Nothing foilTermCons []
    , StandaloneDerivD Nothing [] (AppT (ConT ''Show) (AppT (ConT foilTermT) (VarT n)))
    , DataD [] foilScopeT [PlainTV n ()] Nothing foilScopeCons [DerivClause Nothing [ConT ''Show]]
    , DataD [] foilPatternT [PlainTV n (), PlainTV l ()] Nothing foilPatternCons []
    , StandaloneDerivD Nothing [] (AppT (ConT ''Show) (AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l)))
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toPatternCon :: Name -> Con -> Q Con
    toPatternCon n (NormalC conName params) = do
      (lastScopeName, foilParams) <- toPatternConParams n params
      let foilConName = mkName ("Foil" ++ nameBase conName)
      return (GadtC [foilConName] foilParams (AppT (AppT (ConT foilPatternT) (VarT n)) (VarT lastScopeName)))
      where
        toPatternConParams :: Name -> [BangType] -> Q (Name, [BangType])
        toPatternConParams n [] = return (n, [])
        toPatternConParams n (param@(bang, type_) : params) =
          case type_ of
            ConT tyName | tyName == nameT -> do
              l <- newName "l"
              let type' = AppT (AppT (ConT ''Foil.NameBinder) (VarT n)) (VarT l)
              (l', params') <- toPatternConParams l params
              return (l', (bang, type') : params')
            ConT tyName | tyName == patternT -> do
              l <- newName "l"
              let type' = AppT (AppT (ConT foilPatternT) (VarT n)) (VarT l)
              (l', params') <- toPatternConParams l params
              return (l', (bang, type') : params')
            _ -> do
              (l, params') <- toPatternConParams n params
              return (l, param : params')

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
        foilNames = [n, l]
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, ConT tyName)
          | tyName == patternT = (_bang, foldl AppT (ConT foilPatternT) (map VarT foilNames))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, AppT (ConT foilScopeT) (VarT l))
          | tyName == termT = (_bang, AppT (ConT foilTermT) (VarT n))
        toTermParam _bangType = _bangType
