{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Control.Monad.Foil.TH.MkFoilData (mkFoilData) where

import           Language.Haskell.TH

import qualified Control.Monad.Foil.Internal as Foil
import Control.Monad.Foil.TH.Util

-- | Generate scope-safe variants given names of types for the raw representation.
mkFoilData
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkFoilData termT nameT scopeT patternT = do
  n <- newName "n"
  l <- newName "l"
  TyConI (DataD _ctx _name patternTVars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name scopeTVars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT

  foilPatternCons <- mapM (toPatternCon patternTVars n) patternCons
  let foilScopeCons = map (toScopeCon scopeTVars n) scopeCons
  let foilTermCons = map (toTermCon termTVars n l) termCons

  return
    [ DataD [] foilTermT (termTVars ++ [KindedTV n () (PromotedT ''Foil.S)]) Nothing foilTermCons []
    , DataD [] foilScopeT (scopeTVars ++ [KindedTV n () (PromotedT ''Foil.S)]) Nothing foilScopeCons []
    , DataD [] foilPatternT (patternTVars ++ [KindedTV n () (PromotedT ''Foil.S), KindedTV l () (PromotedT ''Foil.S)]) Nothing foilPatternCons []
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    -- | Convert a constructor declaration for a raw pattern type
    -- into a constructor for the scope-safe pattern type.
    toPatternCon
      :: [TyVarBndr ()]
      -> Name   -- ^ Name for the starting scope type variable.
      -> Con    -- ^ Raw pattern constructor.
      -> Q Con
    toPatternCon tvars n (NormalC conName params) = do
      (lastScopeName, foilParams) <- toPatternConParams 1 n params
      let foilConName = mkName ("Foil" ++ nameBase conName)
      return (GadtC [foilConName] foilParams (PeelConT foilPatternT (map (VarT . tvarName) tvars ++ [VarT n, VarT lastScopeName])))
      where
        -- | Process type parameters of a pattern,
        -- introducing (existential) type variables for the intermediate scopes,
        -- if necessary.
        toPatternConParams
          :: Int                  -- ^ Index of the component in the constructor.
          -> Name                 -- ^ Current scope (after processing any previous bindings).
          -> [BangType]           -- ^ Leftover pattern components.
          -> Q (Name, [BangType]) -- ^ Resulting extended scope and a list of corresponding scope-safe components.
        toPatternConParams _ p [] = return (p, [])
        toPatternConParams i p (param@(bang_, type_) : conParams) =
          case type_ of
            -- if the current component is a variable identifier
            -- then treat it as a single name binder (see 'Foil.NameBinder')
            PeelConT tyName _tyParams | tyName == nameT -> do
              l <- newName ("n" <> show i)
              let type' = AppT (AppT (ConT ''Foil.NameBinder) (VarT p)) (VarT l)
              (l', conParams') <- toPatternConParams (i+1) l conParams
              return (l', (bang_, type') : conParams')
            -- if the current component is a raw pattern
            -- then convert it into a scope-safe pattern
            PeelConT tyName tyParams | tyName == patternT -> do
              l <- newName ("n" <> show i)
              let type' = PeelConT foilPatternT (tyParams ++ [VarT p, VarT l])
              (l', conParams') <- toPatternConParams (i+1) l conParams
              return (l', (bang_, type') : conParams')
            -- otherwise, ignore the component as non-binding
            _ -> do
              (l, conParams') <- toPatternConParams (i+1) p conParams
              return (l, param : conParams')

    -- | Convert a constructor declaration for a raw scoped term
    -- into a constructor for the scope-safe scoped term.
    toScopeCon :: [TyVarBndr ()] -> Name -> Con -> Con
    toScopeCon _tvars n (NormalC conName params) =
      NormalC foilConName (map toScopeParam params)
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        toScopeParam (_bang, PeelConT tyName tyParams)
          | tyName == termT = (_bang, PeelConT foilTermT (tyParams ++ [VarT n]))
        toScopeParam _bangType = _bangType

    -- | Convert a constructor declaration for a raw term
    -- into a constructor for the scope-safe term.
    toTermCon :: [TyVarBndr ()] -> Name -> Name -> Con -> Con
    toTermCon tvars n l (NormalC conName params) =
      GadtC [foilConName] (map toTermParam params) (PeelConT foilTermT (map (VarT . tvarName) tvars ++ [VarT n]))
      where
        foilNames = [n, l]
        foilConName = mkName ("Foil" ++ nameBase conName)
        toTermParam (_bang, PeelConT tyName tyParams)
          | tyName == patternT = (_bang, PeelConT foilPatternT (tyParams ++ map VarT foilNames))
          | tyName == nameT = (_bang, AppT (ConT ''Foil.Name) (VarT n))
          | tyName == scopeT = (_bang, PeelConT foilScopeT (tyParams ++ [VarT l]))
          | tyName == termT = (_bang, PeelConT foilTermT (tyParams ++ [VarT n]))
        toTermParam _bangType = _bangType
