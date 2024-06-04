{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module Control.Monad.Foil.TH.MkToFoil (mkToFoil) where

import           Language.Haskell.TH
import Language.Haskell.TH.Syntax (addModFinalizer)

import qualified Control.Monad.Foil  as Foil
import           Data.Maybe          (catMaybes)
import Data.Map (Map)
import qualified Data.Map as Map

-- | Generate conversion functions from raw to scope-safe representation.
mkToFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkToFoil termT nameT scopeT patternT = do
  extendScopeFoilPattenD <- mkExtendScopeFoilPattern nameT patternT
  withRefreshedFoilPatternD <- mkWithRefreshedFoilPattern nameT patternT
  toFoilTermD <- mkToFoilTerm termT nameT scopeT patternT
  return (
    extendScopeFoilPattenD ++
    withRefreshedFoilPatternD ++
    toFoilTermD
    )

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
        toMatch RecC{} = error "Record constructors (RecC) are not supported yet!"
        toMatch InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
        toMatch ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
        toMatch GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
        toMatch RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"

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

        toMatch (NormalC conName params) =
          Match (ConP foilConName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE scope) sinkFun (ConE foilConName) params

            go _i _scope' f p [] = AppE (AppE (VarE cont) f) p
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
            go i scope' f p (_ : conParams) =
              go (i + 1) scope' f (AppE p (VarE xi)) conParams
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

-- | Generate a conversion function from raw terms to scope-safe terms.
mkToFoilTerm
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkToFoilTerm termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  toFoilTermSignature <-
    SigD toFoilTermT <$>
      [t| forall n. Foil.Distinct n
          => Foil.Scope n
          -> Map $(return (ConT nameT)) (Foil.Name n)
          -> $(return (ConT termT))
          -> $(return (ConT foilTermT)) n
        |]
  toFoilScopedSignature <-
    SigD toFoilScopedT <$>
      [t| forall n. Foil.Distinct n
          => Foil.Scope n
          -> Map $(return (ConT nameT)) (Foil.Name n)
          -> $(return (ConT scopeT))
          -> $(return (ConT foilScopeT)) n
        |]
  toFoilPatternSignature <-
    SigD toFoilPatternT <$>
      [t| forall n r. Foil.Distinct n
          => Foil.Scope n
          -> Map $(return (ConT nameT)) (Foil.Name n)
          -> $(return (ConT patternT))
          -> (forall l. Foil.DExt n l => $(return (ConT foilPatternT)) n l -> Map $(return (ConT nameT)) (Foil.Name l) -> r)
          -> r
        |]

  -- addModFinalizer $ putDoc (DeclDoc toFoilTermT)
    -- "Refresh (if needed) bound variables introduced in a pattern.\nThis is a more flexible version of 'Control.Monad.Foil.withRefreshed'."

  return
    [ toFoilTermSignature
    , toFoilTermBody termCons
    , toFoilPatternSignature
    , toFoilPatternBody patternCons
    , toFoilScopedSignature
    , toFoilScopedBody scopeCons
    ]
  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    toFoilTermT = mkName ("toFoil" ++ nameBase termT)
    toFoilPatternT = mkName ("toFoil" ++ nameBase patternT)
    toFoilScopedT = mkName ("toFoil" ++ nameBase scopeT)

    extendScopePatternFunName = mkName ("extendScopeFoil" ++ nameBase patternT)
    extendScopePatternFun = VarE extendScopePatternFunName

    toFoilTermBody termCons = FunD toFoilTermT
      [Clause [VarP scope, VarP env, VarP term] (NormalB (CaseE (VarE term) (map toMatch termCons))) []]
      where
        scope = mkName "scope"
        env = mkName "env"
        term = mkName "term"

        toMatch (NormalC conName params) =
          Match (ConP conName [] conParamPatterns) (NormalB conMatchBody) [toFoilVarD]
          where
            toFoilVarFunName = mkName "lookupRawVar"
            toFoilVarFun = VarE toFoilVarFunName
            x = mkName "x"
            name = mkName "name"
            toFoilVarD = FunD toFoilVarFunName [Clause [VarP x]
              (NormalB (CaseE (AppE (AppE (VarE 'Map.lookup) (VarE x)) (VarE env))
                [ Match (ConP 'Just [] [VarP name]) (NormalB (VarE name)) []
                , Match (ConP 'Nothing [] []) (NormalB (AppE (VarE 'error) (LitE (StringL "undefined variable")))) []]))
              []]

            conMatchBody = go 1 (VarE scope) (VarE env) (ConE foilConName) params

            go _i _scope' _env' p [] = p
            go i scope' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  go (i+1) scope' env' (AppE p (AppE toFoilVarFun (VarE xi))) conParams
              | tyName == termT =
                  go (i+1) scope' env' (AppE p (AppE (AppE (AppE (VarE toFoilTermT) (VarE scope)) (VarE env)) (VarE xi))) conParams
              | tyName == scopeT =
                  go (i+1) scope' env' (AppE p (AppE (AppE (AppE (VarE toFoilScopedT) scope') env') (VarE xi))) conParams
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE toFoilPatternT) scope') env') (VarE xi))
                    (LamE [VarP xi', VarP envi]
                      (LetE [ValD (VarP scopei) (NormalB (AppE (AppE extendScopePatternFun (VarE xi')) scope')) []]
                        (go (i+1) (VarE scopei) (VarE envi) (AppE p (VarE xi')) conParams)))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                scopei = mkName ("scope" <> show i)
                envi = mkName ("env" <> show i)
            go i scope' env' p (_ : conParams) =
              go (i + 1) scope' env' (AppE p (VarE xi)) conParams
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

    toFoilPatternBody patternCons = FunD toFoilPatternT
      [Clause [VarP scope, VarP env, VarP pattern, VarP cont] (NormalB (CaseE (VarE pattern) (map toMatch patternCons))) []]
      where
        scope = mkName "scope"
        env = mkName "env"
        pattern = mkName "pattern"
        cont = mkName "cont"

        toMatch (NormalC conName params) =
          Match (ConP conName [] conParamPatterns) (NormalB conMatchBody) []
          where
            conMatchBody = go 1 (VarE scope) (VarE env) (ConE foilConName) params

            go _i _scope' env' p [] = AppE (AppE (VarE cont) p) env'
            go i scope' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  AppE (AppE (VarE 'Foil.withFresh) scope')
                    (LamE [VarP xi']
                      (LetE [ ValD (VarP scopei) (NormalB (AppE (AppE (VarE 'Foil.extendScope) (VarE xi')) scope')) []
                            , ValD (VarP envi) (NormalB
                                (AppE (AppE (AppE (VarE 'Map.insert) (VarE xi))
                                  (AppE (VarE 'Foil.nameOf) (VarE xi')))
                                  (InfixE (Just (VarE 'Foil.sink)) (VarE '(<$>)) (Just (VarE envi))))) []]
                        (go (i+1) (VarE scopei) (VarE envi) (AppE p (VarE xi')) conParams)))
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE toFoilPatternT) scope') env') (VarE xi))
                    (LamE [VarP xi', VarP envi]
                      (LetE [ValD (VarP scopei) (NormalB (AppE (AppE extendScopePatternFun (VarE xi')) scope')) []]
                        (go (i+1) (VarE scopei) (VarE envi) (AppE p (VarE xi')) conParams)))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                scopei = mkName ("scope" <> show i)
                envi = mkName ("env" <> show i)
            go i scope' env' p (_ : conParams) =
              go (i + 1) scope' env' (AppE p (VarE xi)) conParams
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

    toFoilScopedBody scopeCons = FunD toFoilScopedT
      [Clause [VarP scope, VarP env, VarP term] (NormalB (CaseE (VarE term) (map toMatch scopeCons))) []]
      where
        scope = mkName "scope"
        env = mkName "env"
        term = mkName "term"

        toMatch (NormalC conName params) =
          Match (ConP conName [] conParamPatterns) (NormalB conMatchBody) [toFoilVarD]
          where
            toFoilVarFunName = mkName "lookupRawVar"
            toFoilVarFun = VarE toFoilVarFunName
            x = mkName "x"
            name = mkName "name"
            toFoilVarD = FunD toFoilVarFunName [Clause [VarP x]
              (NormalB (CaseE (AppE (AppE (VarE 'Map.lookup) (VarE x)) (VarE env))
                [ Match (ConP 'Just [] [VarP name]) (NormalB (VarE name)) []
                , Match (ConP 'Nothing [] []) (NormalB (AppE (VarE 'error) (LitE (StringL "undefined variable")))) []]))
              []]

            conMatchBody = go 1 (VarE scope) (VarE env) (ConE foilConName) params

            go _i _scope' _env' p [] = p
            go i scope' env' p ((_bang, ConT tyName) : conParams)
              | tyName == nameT =
                  go (i+1) scope' env' (AppE p (AppE toFoilVarFun (VarE xi))) conParams
              | tyName == termT =
                  go (i+1) scope' env' (AppE p (AppE (AppE (AppE (VarE toFoilTermT) (VarE scope)) (VarE env)) (VarE xi))) conParams
              | tyName == scopeT =
                  go (i+1) scope' env' (AppE p (AppE (AppE (AppE (VarE toFoilScopedT) scope') env') (VarE xi))) conParams
              | tyName == patternT =
                  AppE
                    (AppE (AppE (AppE (VarE toFoilPatternT) scope') env') (VarE xi))
                    (LamE [VarP xi', VarP envi]
                      (LetE [ValD (VarP scopei) (NormalB (AppE (AppE extendScopePatternFun (VarE xi')) scope')) []]
                        (go (i+1) (VarE scopei) (VarE envi) (AppE p (VarE xi')) conParams)))
              where
                xi = mkName ("x" <> show i)
                xi' = mkName ("x" <> show i <> "'")
                scopei = mkName ("scope" <> show i)
                envi = mkName ("env" <> show i)
            go i scope' env' p (_ : conParams) =
              go (i + 1) scope' env' (AppE p (VarE xi)) conParams
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
