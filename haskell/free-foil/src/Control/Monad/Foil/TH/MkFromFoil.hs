{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module Control.Monad.Foil.TH.MkFromFoil (mkFromFoil) where

import           Language.Haskell.TH
import Language.Haskell.TH.Syntax (addModFinalizer)

import qualified Control.Monad.Foil  as Foil

-- | Generate conversion functions from raw to scope-safe representation.
mkFromFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkFromFoil termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  fromFoilTermSignature <-
    SigD fromFoilTermT <$>
      [t| forall n.
          [$(return (ConT nameT))]
          -> Foil.NameMap n $(return (ConT nameT))
          -> $(return (ConT foilTermT)) n
          -> $(return (ConT termT))
        |]
  fromFoilScopedSignature <-
    SigD fromFoilScopedT <$>
      [t| forall n.
          [$(return (ConT nameT))]
          -> Foil.NameMap n $(return (ConT nameT))
          -> $(return (ConT foilScopeT)) n
          -> $(return (ConT scopeT))
        |]
  fromFoilPatternSignature <-
    SigD fromFoilPatternT <$>
      [t| forall n l r.
          [$(return (ConT nameT))]
          -> Foil.NameMap n $(return (ConT nameT))
          -> $(return (ConT foilPatternT)) n l
          -> ([$(return (ConT nameT))] -> Foil.NameMap l $(return (ConT nameT)) -> $(return (ConT patternT)) -> r)
          -> r
        |]

  addModFinalizer $ putDoc (DeclDoc fromFoilTermT)
    "Convert a scope-safe term into a raw term."
  addModFinalizer $ putDoc (DeclDoc fromFoilPatternT)
    "Convert a scope-safe pattern into a raw pattern."
  addModFinalizer $ putDoc (DeclDoc fromFoilScopedT)
    "Convert a scope-safe scoped term into a raw scoped term."

  return
    [ fromFoilTermSignature
    , fromFoilTermBody termCons
    , fromFoilPatternSignature
    , fromFoilPatternBody patternCons
    , fromFoilScopedSignature
    , fromFoilScopedBody scopeCons
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    fromFoilTermT = mkName ("fromFoil" ++ nameBase termT)
    fromFoilPatternT = mkName ("fromFoil" ++ nameBase patternT)
    fromFoilScopedT = mkName ("fromFoil" ++ nameBase scopeT)

    fromFoilTermBody termCons = FunD fromFoilTermT
      [Clause [VarP freshVars, VarP env, VarP term] (NormalB (CaseE (VarE term) (map toMatch termCons))) []]
      where
        freshVars = mkName "freshVars"
        env = mkName "env"
        term = mkName "term"

        toMatch (NormalC conName params) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE freshVars) (VarE env) (ConE conName) params

            go _i _freshVars' _env' p [] = p
            go i freshVars' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (VarE 'Foil.lookupName) (VarE xi)) env')) conParams
              | tyName == termT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (AppE (VarE fromFoilTermT) (VarE freshVars)) (VarE env)) (VarE xi))) conParams
              | tyName == scopeT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (AppE (VarE fromFoilScopedT) freshVars') env') (VarE xi))) conParams
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE fromFoilPatternT) freshVars') env') (VarE xi))
                    (LamE [VarP freshVarsi, VarP envi, VarP xi']
                      (go (i+1) (VarE freshVarsi) (VarE envi) (AppE p (VarE xi')) conParams))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                freshVarsi = mkName ("freshVars" <> show i)
                envi = mkName ("env" <> show i)
            go i freshVars' env' p (_ : conParams) =
              go (i + 1) freshVars' env' (AppE p (VarE xi)) conParams
              where
                xi = mkName ("x" <> show i)

            foilConName = mkName ("Foil" ++ nameBase conName)
            conParamPatterns = map VarP conParamVars

            conParamVars = zipWith mkConParamVar params [1..]

            mkConParamVar :: BangType -> Int -> Name
            mkConParamVar _ty i = mkName ("x" <> show i)
        toMatch RecC{} = error "Record constructors (RecC) are not supported yet!"
        toMatch InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
        toMatch ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
        toMatch GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
        toMatch RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"

    fromFoilPatternBody patternCons = FunD fromFoilPatternT
      [Clause [VarP freshVars, VarP env, VarP pattern, VarP cont] (NormalB (CaseE (VarE pattern) (map toMatch patternCons))) []]
      where
        freshVars = mkName "freshVars"
        env = mkName "env"
        pattern = mkName "pattern"
        cont = mkName "cont"

        toMatch (NormalC conName params) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE freshVars) (VarE env) (ConE conName) params

            go _i freshVars' env' p [] = AppE (AppE (AppE (VarE cont) freshVars') env') p
            go i freshVars' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  CaseE freshVars'
                    [ Match (ListP []) (NormalB (AppE (VarE 'error) (LitE (StringL "not enough fresh variables")))) []
                    , Match (InfixP (VarP var) '(:) (VarP vars))
                        (NormalB (LetE
                          [ValD (VarP envi) (NormalB (AppE (AppE (AppE (VarE 'Foil.addNameBinder) (VarE xi)) (VarE var)) env')) []]
                          (go (i + 1) (VarE vars) (VarE envi) (AppE p (VarE var)) conParams)))
                        []
                    ]
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE fromFoilPatternT) freshVars') env') (VarE xi))
                    (LamE [VarP freshVarsi, VarP envi, VarP xi']
                      (go (i+1) (VarE freshVarsi) (VarE envi) (AppE p (VarE xi')) conParams))
              where
                var = mkName "var"
                vars = mkName "vars"
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                freshVarsi = mkName ("freshVars" <> show i)
                envi = mkName ("env" <> show i)
            go i freshVars' env' p (_ : conParams) =
              go (i + 1) freshVars' env' (AppE p (VarE xi)) conParams
              where
                xi = mkName ("x" <> show i)

            foilConName = mkName ("Foil" ++ nameBase conName)
            conParamPatterns = map VarP conParamVars

            conParamVars = zipWith mkConParamVar params [1..]

            mkConParamVar :: BangType -> Int -> Name
            mkConParamVar _ i = mkName ("x" <> show i)
        toMatch RecC{} = error "Record constructors (RecC) are not supported yet!"
        toMatch InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
        toMatch ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
        toMatch GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
        toMatch RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"

    fromFoilScopedBody freshVarsCons = FunD fromFoilScopedT
      [Clause [VarP freshVars, VarP env, VarP term] (NormalB (CaseE (VarE term) (map toMatch freshVarsCons))) []]
      where
        freshVars = mkName "freshVars"
        env = mkName "env"
        term = mkName "term"

        toMatch (NormalC conName params) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE freshVars) (VarE env) (ConE conName) params

            go _i _freshVars' _env' p [] = p
            go i freshVars' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (VarE 'Foil.lookupName) (VarE xi)) env')) conParams
              | tyName == termT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (AppE (VarE fromFoilTermT) (VarE freshVars)) (VarE env)) (VarE xi))) conParams
              | tyName == scopeT =
                  go (i+1) freshVars' env' (AppE p (AppE (AppE (AppE (VarE fromFoilScopedT) freshVars') env') (VarE xi))) conParams
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE fromFoilPatternT) freshVars') env') (VarE xi))
                    (LamE [VarP freshVarsi, VarP envi, VarP xi']
                      (go (i+1) (VarE freshVarsi) (VarE envi) (AppE p (VarE xi')) conParams))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                freshVarsi = mkName ("freshVars" <> show i)
                envi = mkName ("env" <> show i)
            go i freshVars' env' p (_ : conParams) =
              go (i + 1) freshVars' env' (AppE p (VarE xi)) conParams
              where
                xi = mkName ("x" <> show i)

            foilConName = mkName ("Foil" ++ nameBase conName)
            conParamPatterns = map VarP conParamVars

            conParamVars = zipWith mkConParamVar params [1..]

            mkConParamVar :: BangType -> Int -> Name
            mkConParamVar _ty i = mkName ("x" <> show i)
        toMatch RecC{} = error "Record constructors (RecC) are not supported yet!"
        toMatch InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
        toMatch ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
        toMatch GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
        toMatch RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"
