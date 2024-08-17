{-# OPTIONS_GHC -fno-warn-type-defaults      #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Free.Foil.TH.Convert where

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import           Control.Monad.Foil.TH.Util

-- * Bulk generators

-- | Generate helpers for conversion to scope-safe representation.
-- Includes 'mkConvertToSig', 'mkGetPatternBinder', and 'mkGetScopedTerm'.
mkConvertToFreeFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkConvertToFreeFoil termT nameT scopeT patternT = concat <$> sequence
  [ mkConvertToSig termT nameT scopeT patternT
  , mkGetPatternBinder nameT patternT
  , mkGetScopedTerm termT scopeT
  ]

-- | Generate helpers for conversion from scope-safe representation.
-- Includes 'mkConvertFromSig'.
mkConvertFromFreeFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkConvertFromFreeFoil termT nameT scopeT patternT = concat <$> sequence
  [ mkConvertFromSig termT nameT scopeT patternT
  ]

-- * Individual generators

-- | Generate conversion helper that goes unpeels one node from a raw term.
mkConvertToSig
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkConvertToSig termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT
  TyConI (NewtypeD _ctx _name nameTVars _kind _nameCons _deriv) <- reify nameT

  convertTermToSigClauses <- concat <$> mapM toClause termCons

  let params = map (VarT . tvarName) termTVars
      termType = return $ PeelConT termT params
      nameType = return $ PeelConT nameT (map (VarT . tvarName) nameTVars)
      scopeType = return $ PeelConT scopeT params
      patternType = return $ PeelConT patternT params
      signatureType = return $ PeelConT signatureT params
  convertTermToSigClausesType <-
    [t| $termType -> Either $nameType ($signatureType ($patternType, $scopeType) $termType) |]

  addModFinalizer $ putDoc (DeclDoc convertTermToSigT)
    ("/Generated/ with '" ++ show 'mkConvertToSig ++ "'. Perform one step of converting '" ++ show termT ++ "', peeling off one node of type '" ++ show signatureT ++ "'.")
  return
    [ SigD convertTermToSigT convertTermToSigClausesType
    , FunD convertTermToSigT convertTermToSigClauses
    ]
  where
    signatureT = mkName (nameBase termT ++ "Sig")
    convertTermToSigT = mkName ("convertTo" ++ nameBase signatureT)

    toClause :: Con -> Q [Clause]
    toClause = \case
      NormalC conName types | any isVarP pats
        -> return [Clause [ConP conName [] pats] (NormalB (AppE (ConE 'Left) (VarE x))) []]
        where
          x = mkName "x"
          isVarP VarP{} = True
          isVarP _      = False
          pats =
            [ case type_ of
                PeelConT typeName _ | typeName == nameT -> VarP x
                _                                       -> WildP
            | (_bang, type_) <- types ]
      NormalC conName types -> mkClause conName conName' types
        where
          conName' = mkName (nameBase conName ++ "Sig")
      RecC conName types -> toClause (NormalC conName (map removeName types))
      InfixC l conName r -> mkClause conName conName' [l, r]
        where
          conName' = mkName (nameBase conName ++ "---")
      ForallC _ _ con -> toClause con
      GadtC conNames types _retType -> concat <$> mapM (\conName -> toClause (NormalC conName types)) conNames
      RecGadtC conNames types retType -> toClause (GadtC conNames (map removeName types) retType)

    mkClause conName conName' types = return
      [ Clause [ConP conName [] pats] (NormalB (AppE (ConE 'Right) (foldl AppE (ConE conName') (concat args)))) [] ]
      where
        p = mkName "p"
        (pats, args) = unzip
          [ case type_ of
              PeelConT typeName _
                | typeName == patternT -> (VarP p, [])
                | typeName == scopeT -> (VarP x, [TupE [Just (VarE p), Just (VarE x)]])
              _ -> (VarP x, [VarE x])
          | (i, (_bang, type_)) <- zip [0..] types
          , let x = mkName ("x" ++ show i)
          ]

-- | Generate conversion helper that peels back one node to a raw term.
mkConvertFromSig
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkConvertFromSig termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT
  TyConI (NewtypeD _ctx _name _nameTVars _kind _nameCons _deriv) <- reify nameT

  convertTermFromSigClauses <- concat <$> mapM toClause termCons

  let params = map (VarT . tvarName) termTVars
      termType = return $ PeelConT termT params
      scopeType = return $ PeelConT scopeT params
      patternType = return $ PeelConT patternT params
      signatureType = return $ PeelConT signatureT params
  convertTermFromSigClausesType <-
    [t| $signatureType ($patternType, $scopeType) $termType -> $termType |]

  addModFinalizer $ putDoc (DeclDoc convertTermFromSigT)
    ("/Generated/ with '" ++ show 'mkConvertFromSig ++ "'. Perform one step of converting '" ++ show termT ++ "', peeling off one node of type '" ++ show signatureT ++ "'.")
  return
    [ SigD convertTermFromSigT convertTermFromSigClausesType
    , FunD convertTermFromSigT convertTermFromSigClauses
    ]
  where
    signatureT = mkName (nameBase termT ++ "Sig")
    convertTermFromSigT = mkName ("convertFrom" ++ nameBase signatureT)

    toClause :: Con -> Q [Clause]
    toClause = \case
      NormalC _conName types | or [ typeName == nameT | (_bang, PeelConT typeName _typeParams) <- types ]
        -> pure []
      NormalC conName types -> mkClause conName conName' types
        where
          conName' = mkName (nameBase conName ++ "Sig")
      RecC conName types -> toClause (NormalC conName (map removeName types))
      InfixC l conName r -> mkClause conName conName' [l, r]
        where
          conName' = mkName (nameBase conName ++ "---")
      ForallC _ _ con -> toClause con
      GadtC conNames types _retType -> concat <$> mapM (\conName -> toClause (NormalC conName types)) conNames
      RecGadtC conNames types retType -> toClause (GadtC conNames (map removeName types) retType)

    mkClause conName conName' types = return
      [ Clause [ConP conName' [] (concat pats)] (NormalB (foldl AppE (ConE conName) args)) [] ]
      where
        p = mkName "p"
        (args, pats) = unzip
          [ case type_ of
              PeelConT typeName _
                | typeName == patternT -> (VarE p, [])
                | typeName == scopeT -> (VarE x, [TupP [VarP p, VarP x]])
              _ -> (VarE x, [VarP x])
          | (i, (_bang, type_)) <- zip [0..] types
          , let x = mkName ("x" ++ show i)
          ]

-- | Generate a helper that extracts at most one binder from a pattern.
mkGetPatternBinder
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkGetPatternBinder nameT patternT = do
  TyConI (NewtypeD _ctx _name nameTVars _kind _nameCons _deriv) <- reify nameT
  TyConI (DataD _ctx _name patternTVars _kind patternCons _deriv) <- reify patternT

  getPatternBinderClauses <- concat <$> mapM toClause patternCons

  let nameType = return $ PeelConT nameT (map (VarT . tvarName) nameTVars)
      patternType = return $ PeelConT patternT (map (VarT . tvarName) patternTVars)
  getPatternBinderClausesType <-
    [t| $patternType -> Maybe $nameType |]

  addModFinalizer $ putDoc (DeclDoc getPatternBinderT)
    ("/Generated/ with '" ++ show 'mkGetPatternBinder ++ "'. Extract at most one binder from a pattern or __crash__.")
  return
    [ SigD getPatternBinderT getPatternBinderClausesType
    , FunD getPatternBinderT getPatternBinderClauses
    ]
  where
    getPatternBinderT = mkName ("get" ++ nameBase patternT ++ "Binder")

    toClause :: Con -> Q [Clause]
    toClause = \case
      NormalC conName types -> mkClause conName types
      RecC conName types -> toClause (NormalC conName (map removeName types))
      InfixC l conName r -> toClause (NormalC conName [l, r])
      ForallC _ _ con -> toClause con
      GadtC conNames types _retType -> concat <$> mapM (\conName -> mkClause conName types) conNames
      RecGadtC conNames types retType -> toClause (GadtC conNames (map removeName types) retType)

    mkClause :: Name -> [BangType] -> Q [Clause]
    mkClause conName types = do
      body <- case concat vars of
        []       -> [e| Nothing |]
        [Just y] -> [e| Just $y |]
        _        -> [e| error "complex patterns are not supported" |]
      return [ Clause [ConP conName [] pats] (NormalB body) [] ]
      where
        x = mkName "x"
        (pats, vars) = unzip
          [ case type_ of
              PeelConT typeName _
                | typeName == nameT -> (VarP x, [Just (return (VarE x))])
                | typeName == patternT -> (WildP, [Nothing])
              _ -> (WildP, [])
          | (_bang, type_) <- types
          ]

-- | Generate a helper that extracts a term from a scoped term.
mkGetScopedTerm
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw scoped terms.
  -> Q [Dec]
mkGetScopedTerm termT scopeT = do
  TyConI (DataD _ctx _name termTVars _kind _termCons _deriv) <- reify termT
  TyConI (DataD _ctx _name _scopeTVars _kind scopeCons _deriv) <- reify scopeT

  getScopedTermClauses <- concat <$> mapM toClause scopeCons

  let params = map (VarT . tvarName) termTVars
      termType = return $ PeelConT termT params
      scopeType = return $ PeelConT scopeT params
  getScopedTermClausesType <-
    [t| $scopeType -> $termType |]

  addModFinalizer $ putDoc (DeclDoc getScopedTermT)
    ("/Generated/ with '" ++ show 'mkGetScopedTerm ++ "'. Extract scoped term or __crash__.")
  return
    [ SigD getScopedTermT getScopedTermClausesType
    , FunD getScopedTermT getScopedTermClauses
    ]
  where
    getScopedTermT = mkName ("get" ++ nameBase termT ++ "From" ++ nameBase scopeT)

    toClause :: Con -> Q [Clause]
    toClause = \case
      NormalC conName types -> mkClause conName types
      RecC conName types -> toClause (NormalC conName (map removeName types))
      InfixC l conName r -> toClause (NormalC conName [l, r])
      ForallC _ _ con -> toClause con
      GadtC conNames types _retType -> concat <$> mapM (\conName -> mkClause conName types) conNames
      RecGadtC conNames types retType -> toClause (GadtC conNames (map removeName types) retType)

    mkClause :: Name -> [BangType] -> Q [Clause]
    mkClause conName types = do
      body <- case concat vars of
        [y] -> [e| $y |]
        _   -> [e| error "complex patterns are not supported" |]
      return [ Clause [ConP conName [] pats] (NormalB body) [] ]
      where
        x = mkName "x"
        (pats, vars) = unzip
          [ case type_ of
              PeelConT typeName _
                | typeName == termT -> (VarP x, [return (VarE x)])
              _ -> (WildP, [])
          | (_bang, type_) <- types
          ]
