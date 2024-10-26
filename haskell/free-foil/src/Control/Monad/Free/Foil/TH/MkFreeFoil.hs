{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
module Control.Monad.Free.Foil.TH.MkFreeFoil where

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (addModFinalizer)

import           Control.Monad              (forM, forM_, when)
import qualified Control.Monad.Foil         as Foil
import           Control.Monad.Foil.TH.Util
import qualified Control.Monad.Free.Foil    as Foil
import           Data.Bifunctor
import           Data.List                  (find, unzip4, (\\))
import           Data.Maybe                 (catMaybes, mapMaybe)
import qualified GHC.Generics               as GHC

type NameOfIdent = Name

data FreeFoilTermConfig = FreeFoilTermConfig
  { rawIdentName          :: NameOfIdent
  , rawTermName           :: Name
  , rawBindingName        :: Name
  , rawScopeName          :: Name
  , rawVarConName         :: Name
  , rawSubTermNames       :: [Name]
  , intToRawIdentName     :: Name
  , rawVarIdentToTermName :: Name
  , rawTermToScopeName    :: Name
  }

data FreeFoilConfig = FreeFoilConfig
  { rawQuantifiedNames        :: [Name]
  , freeFoilTermConfigs       :: [FreeFoilTermConfig]
  , freeFoilNameModifier      :: String -> String
  , freeFoilScopeNameModifier :: String -> String
  , signatureNameModifier     :: String -> String
  , freeFoilConNameModifier   :: String -> String
  , freeFoilConvertToName     :: String -> String
  , freeFoilConvertFromName   :: String -> String
  , ignoreNames               :: [Name]
  }

toFreeFoilName :: FreeFoilConfig -> Name -> Name
toFreeFoilName FreeFoilConfig{..} name = mkName (freeFoilNameModifier (nameBase name))

toFreeFoilNameFrom :: FreeFoilConfig -> Name -> Name
toFreeFoilNameFrom FreeFoilConfig{..} name = mkName (freeFoilConvertFromName (nameBase name))

toFreeFoilNameTo :: FreeFoilConfig -> Name -> Name
toFreeFoilNameTo FreeFoilConfig{..} name = mkName (freeFoilConvertToName (nameBase name))

toFreeFoilScopedName :: FreeFoilConfig -> Name -> Name
toFreeFoilScopedName FreeFoilConfig{..} name = mkName (freeFoilScopeNameModifier (nameBase name))

toSignatureName :: FreeFoilConfig -> Name -> Name
toSignatureName FreeFoilConfig{..} name = mkName (signatureNameModifier (nameBase name))

toConName :: FreeFoilConfig -> Name -> Name
toConName FreeFoilConfig{..} name = mkName (freeFoilConNameModifier (nameBase name))

lookupIdentName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupIdentName name = find (\FreeFoilTermConfig{..} -> rawIdentName == name)

lookupTermName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupTermName name = find (\FreeFoilTermConfig{..} -> rawTermName == name)

lookupSubTermName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupSubTermName name = find (\FreeFoilTermConfig{..} -> name `elem` rawSubTermNames)

lookupBindingName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupBindingName name = find (\FreeFoilTermConfig{..} -> rawBindingName == name)

lookupScopeName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupScopeName name = find (\FreeFoilTermConfig{..} -> rawScopeName == name)

data Sort
  = SortBinder | SortTerm | SortSubTerm

toFreeFoilType :: Sort -> FreeFoilConfig -> Type -> Type -> Type -> Type
toFreeFoilType isBinder config@FreeFoilConfig{..} outerScope innerScope = go
  where
    go = \case
      PeelConT typeName (map go -> typeParams)
        | typeName `elem` rawQuantifiedNames ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
        | typeName `elem` map rawIdentName freeFoilTermConfigs ->
            case isBinder of
              SortBinder -> PeelConT ''Foil.NameBinder [outerScope, innerScope]
              _          -> PeelConT ''Foil.Name [outerScope]
        | Just _ <- lookupTermName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope, innerScope])
        | Just FreeFoilTermConfig{..} <- lookupScopeName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config rawTermName) (typeParams ++ [innerScope])
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
      ForallT bndrs ctx type_ -> ForallT bndrs ctx (go type_)
      ForallVisT bndrs type_ -> ForallVisT bndrs (go type_)
      AppT f x -> AppT (go f) (go x)
      AppKindT f k -> AppKindT (go f) k
      SigT t k -> SigT (go t) k
      t@ConT{} -> t
      t@VarT{} -> t
      t@PromotedT{} -> t
      InfixT l op r -> InfixT (go l) op (go r)
      UInfixT l op r -> UInfixT (go l) op (go r)
      PromotedInfixT l op r -> PromotedInfixT (go l) op (go r)
      PromotedUInfixT l op r -> PromotedUInfixT (go l) op (go r)
      ParensT t -> ParensT (go t)
      t@TupleT{} -> t
      t@UnboxedTupleT{} -> t
      t@UnboxedSumT{} -> t
      t@ArrowT{} -> t
      t@MulArrowT{} -> t
      t@EqualityT{} -> t
      t@ListT{} -> t
      t@PromotedTupleT{} -> t
      t@PromotedNilT{} -> t
      t@PromotedConsT{} -> t
      t@StarT{} -> t
      t@ConstraintT{} -> t
      t@LitT{} -> t
      t@WildCardT{} -> t
      ImplicitParamT s t -> ImplicitParamT s (go t)

toFreeFoilSigType :: Sort -> FreeFoilConfig -> Type -> Type -> Type -> Maybe Type
toFreeFoilSigType sort config@FreeFoilConfig{..} scope term = go
  where
    go :: Type -> Maybe Type
    go = \case
      PeelConT _typeName (mapM go -> Nothing) ->
        error "bad type params"
      PeelConT typeName (mapM go -> Just typeParams)
        | Just _ <- lookupTermName typeName freeFoilTermConfigs ->
            case sort of
              SortSubTerm -> Just (PeelConT (toSignatureName config typeName) (typeParams ++ [scope, term]))
              _           -> Just term
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs ->
            Nothing
        | Just _ <- lookupScopeName typeName freeFoilTermConfigs ->
            Just scope
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs ->
            Just (PeelConT (toSignatureName config typeName) (typeParams ++ [scope, term]))
      ForallT bndrs ctx type_ -> ForallT bndrs ctx <$> go type_
      ForallVisT bndrs type_ -> ForallVisT bndrs <$> go type_
      AppT f x -> AppT <$> go f <*> go x
      AppKindT f k -> AppKindT <$> go f <*> pure k
      SigT t k -> SigT <$> go t <*> pure k
      t@ConT{} -> pure t
      t@VarT{} -> pure t
      t@PromotedT{} -> pure t
      InfixT l op r -> InfixT <$> go l <*> pure op <*> go r
      UInfixT l op r -> UInfixT <$> go l <*> pure op <*> go r
      PromotedInfixT l op r -> PromotedInfixT <$> go l <*> pure op <*> go r
      PromotedUInfixT l op r -> PromotedUInfixT <$> go l <*> pure op <*> go r
      ParensT t -> ParensT <$> go t
      t@TupleT{} -> pure t
      t@UnboxedTupleT{} -> pure t
      t@UnboxedSumT{} -> pure t
      t@ArrowT{} -> pure t
      t@MulArrowT{} -> pure t
      t@EqualityT{} -> pure t
      t@ListT{} -> pure t
      t@PromotedTupleT{} -> pure t
      t@PromotedNilT{} -> pure t
      t@PromotedConsT{} -> pure t
      t@StarT{} -> pure t
      t@ConstraintT{} -> pure t
      t@LitT{} -> pure t
      t@WildCardT{} -> pure t
      ImplicitParamT s t -> ImplicitParamT s <$> go t

toFreeFoilCon :: FreeFoilConfig -> Type -> Type -> Type -> Con -> Q Con
toFreeFoilCon config rawRetType outerScope innerScope = go
  where
    goType = toFreeFoilType SortTerm config outerScope innerScope
    go = \case
      GadtC conNames argTypes retType -> do
        let newConNames = map (toConName config) conNames
        forM_ (zip conNames newConNames) $ \(conName, newConName) ->
          addModFinalizer $ putDoc (DeclDoc newConName)
            ("Corresponds to '" ++ show conName ++ "'.")
        return (GadtC newConNames (map (fmap goType) argTypes) (goType retType))
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC params ctx con -> ForallC params ctx <$> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

toFreeFoilSigCon :: FreeFoilConfig -> FreeFoilTermConfig -> Name -> Type -> Type -> Type -> Con -> Q (Maybe Con)
toFreeFoilSigCon config FreeFoilTermConfig{..} sigName rawRetType scope term = go
  where
    goType = toFreeFoilSigType SortTerm config scope term
    go = \case
      GadtC conNames argTypes retType
        | null newConNames -> pure Nothing
        | otherwise -> do
            forM_ (zip conNames newConNames) $ \(conName, newConName) ->
              addModFinalizer $ putDoc (DeclDoc newConName)
                ("Corresponds to '" ++ show conName ++ "'.")
            return (Just (GadtC newConNames newArgTypes theRetType))
        where
          newArgTypes = mapMaybe (traverse goType) argTypes
          newConNames =
            [ toSignatureName config rawConName
            | rawConName <- conNames
            , rawConName /= rawVarConName ]
          theRetType =
            case retType of
              PeelConT _rawTypeName (mapM goType -> Just params) ->
                PeelConT sigName (params ++ [scope, term])
              _ -> error "unexpected return type!"
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC params ctx con -> fmap (ForallC params ctx) <$> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

toFreeFoilBindingCon :: FreeFoilConfig -> Type -> Type -> Con -> Q Con
toFreeFoilBindingCon config rawRetType theOuterScope = go
  where
    goType = toFreeFoilType SortBinder config theOuterScope

    goTypeArgs :: Int -> Type -> [BangType] -> Q (Type, [BangType])
    goTypeArgs _ outerScope [] = pure (outerScope, [])
    goTypeArgs i outerScope ((bang_, rawArgType) : rawArgs) = do
      case rawArgType of
        PeelConT rawTypeName _rawTypeParams
          | rawTypeName `elem` map rawIdentName (freeFoilTermConfigs config) -> do
            innerScope <- VarT <$> newName ("i" <> show i)
            let argType = toFreeFoilType SortBinder config outerScope innerScope rawArgType
            (theInnerScope, argTypes) <- goTypeArgs (i + 1) innerScope rawArgs
            return (theInnerScope, ((bang_, argType) : argTypes))

          | Just _ <- lookupBindingName rawTypeName (freeFoilTermConfigs config) -> do
            innerScope <- VarT <$> newName ("i" <> show i)
            let argType = toFreeFoilType SortBinder config outerScope innerScope rawArgType
            (theInnerScope, argTypes) <- goTypeArgs (i + 1) innerScope rawArgs
            return (theInnerScope, ((bang_, argType) : argTypes))

        _ -> do
          let argType = toFreeFoilType SortBinder config outerScope outerScope rawArgType
          (theInnerScope, argTypes) <- goTypeArgs (i + 1) outerScope rawArgs
          return (theInnerScope, ((bang_, argType) : argTypes))

    go :: Con -> Q Con
    go = \case
      GadtC conNames argTypes retType -> do
        (theInnerScope, newArgs) <- goTypeArgs 0 theOuterScope argTypes
        let newConNames = map (toConName config) conNames
        forM_ (zip conNames newConNames) $ \(conName, newConName) ->
          addModFinalizer $ putDoc (DeclDoc newConName)
            ("Corresponds to '" ++ show conName ++ "'.")
        return (GadtC newConNames newArgs (goType theInnerScope retType))
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC params ctx con -> ForallC params ctx <$> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

termConToPat :: Name -> FreeFoilConfig -> FreeFoilTermConfig -> Con -> Q [([Name], Pat, Pat, [Exp])]
termConToPat rawTypeName config@FreeFoilConfig{..} FreeFoilTermConfig{..} = go
  where
    rawRetType = error "impossible happened!"

    fromArgType :: Type -> Q ([Name], [Pat], [Pat], [Exp])
    fromArgType = \case
      PeelConT typeName _params
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs -> do
            return ([], [], [], [])
        | Just _ <- lookupScopeName typeName freeFoilTermConfigs -> do
            binder <- newName "binder"
            body <- newName "body"
            return ([binder, body], [ConP 'Foil.ScopedAST [] [VarP binder, VarP body]], [TupP [VarP binder, VarP body]], [VarE binder, VarE body])
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameFrom config rawSigName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (VarE funName) (VarE x)])
        | typeName == '[] -> do
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [ConE 'False])
      AppT _ (PeelConT typeName _params)
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameFrom config rawSigName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (AppE (VarE 'fmap) (VarE funName)) (VarE x)])
      _ -> do
        x <- newName "x"
        return ([x], [VarP x], [VarP x], [VarE x])

    go :: Con -> Q [([Name], Pat, Pat, [Exp])]
    go = \case
      GadtC conNames rawArgTypes _rawRetType -> concat <$> do
        forM conNames $ \conName -> do
          let newConName = toSignatureName config conName
          (concat -> vars, concat -> pats, concat -> pats', concat -> exps) <- unzip4 <$>
            mapM (fromArgType . snd) rawArgTypes
          return $
            if rawTypeName == rawTermName
              then [ (vars, ConP 'Foil.Node [] [ConP newConName [] pats], ConP newConName [] pats', exps) ]
              else [ (vars, ConP newConName [] pats, ConP newConName [] pats', exps) ]
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

termConToPatBinding :: Name -> FreeFoilConfig -> FreeFoilTermConfig -> Con -> Q [([Name], Pat, Pat, [Exp])]
termConToPatBinding rawTypeName config@FreeFoilConfig{..} FreeFoilTermConfig{..} = go
  where
    rawRetType = error "impossible happened!"

    fromArgType :: Type -> Q ([Name], [Pat], [Pat], [Exp])
    fromArgType = \case
      PeelConT typeName _params
        | typeName == rawIdentName -> do
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE intToRawIdentName `AppE` (VarE 'Foil.nameId `AppE` (VarE 'Foil.nameOf `AppE` VarE x))])
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config typeName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE funName `AppE` VarE x])
        | Just _ <- lookupScopeName typeName freeFoilTermConfigs -> do
            binder <- newName "binder"
            body <- newName "body"
            return ([binder, body], [ConP 'Foil.ScopedAST [] [VarP binder, VarP body]], [TupP [VarP binder, VarP body]], [VarE binder, VarE body])
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameFrom config rawSigName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (VarE funName) (VarE x)])
      AppT _ (PeelConT typeName _params)
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameFrom config rawSigName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (AppE (VarE 'fmap) (VarE funName)) (VarE x)])
      _ -> do
        x <- newName "x"
        return ([x], [VarP x], [VarP x], [VarE x])

    go :: Con -> Q [([Name], Pat, Pat, [Exp])]
    go = \case
      GadtC conNames rawArgTypes _rawRetType -> concat <$> do
        forM conNames $ \conName -> do
          let newConName = toFreeFoilName config conName
          (concat -> vars, concat -> pats, concat -> pats', concat -> exps) <- unzip4 <$>
            mapM (fromArgType . snd) rawArgTypes
          return $
            if rawTypeName == rawTermName
              then [ (vars, ConP 'Foil.Node [] [ConP newConName [] pats], ConP newConName [] pats', exps) ]
              else [ (vars, ConP newConName [] pats, ConP newConName [] pats', exps) ]
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

termConToPatQualified :: FreeFoilConfig -> Con -> Q [([Name], Pat, Pat, [Exp])]
termConToPatQualified config@FreeFoilConfig{..} = go
  where
    rawRetType = error "impossible happened!"

    fromArgType :: Type -> Q ([Name], [Pat], [Pat], [Exp])
    fromArgType = \case
      PeelConT typeName _params
        | Just _ <- lookupTermName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config typeName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE funName `AppE` VarE x])
        | Just FreeFoilTermConfig{..} <- lookupScopeName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config rawTermName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE rawTermToScopeName `AppE` (VarE funName `AppE` VarE x)])
        | Just FreeFoilTermConfig{..} <- lookupIdentName typeName freeFoilTermConfigs -> do
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE intToRawIdentName `AppE` (VarE 'Foil.nameId `AppE` VarE x)])
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config typeName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [VarE funName `AppE` VarE x])
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameFrom config rawSigName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (VarE funName) (VarE x)])
      AppT _ (PeelConT typeName _params)
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config typeName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (AppE (VarE 'fmap) (VarE funName)) (VarE x)])
        | Just _ <- lookupTermName typeName freeFoilTermConfigs -> do
            let funName = toFreeFoilNameFrom config typeName
            x <- newName "x"
            return ([x], [VarP x], [VarP x], [AppE (AppE (VarE 'fmap) (VarE funName)) (VarE x)])
      _ -> do
        x <- newName "x"
        return ([x], [VarP x], [VarP x], [VarE x])

    go :: Con -> Q [([Name], Pat, Pat, [Exp])]
    go = \case
      GadtC conNames rawArgTypes _rawRetType -> concat <$> do
        forM conNames $ \conName -> do
          let newConName = toFreeFoilName config conName
          (concat -> vars, concat -> pats, concat -> pats', concat -> exps) <- unzip4 <$>
            mapM (fromArgType . snd) rawArgTypes
          return [ (vars, ConP newConName [] pats, ConP newConName [] pats', exps) ]
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

mkPatternSynonym :: Name -> FreeFoilConfig -> FreeFoilTermConfig -> Type -> Con -> Q [Dec]
mkPatternSynonym rawTypeName config termConfig@FreeFoilTermConfig{..} rawRetType = go
  where
    go :: Con -> Q [Dec]
    go = \case
      GadtC conNames rawArgTypes _rawRetType -> concat <$> do
        forM (conNames \\ [rawVarConName]) $ \conName -> do
          let patName = toConName config conName
              rawConType = foldr (\x y -> AppT (AppT ArrowT x) y) rawRetType (map snd rawArgTypes)
              outerScope = VarT (mkName "o")
              innerScope = VarT (mkName "i")
          [(vars, pat, _, _)] <- termConToPat rawTypeName config termConfig (GadtC [conName] rawArgTypes rawRetType)    -- FIXME: unsafe matching!
          addModFinalizer $ putDoc (DeclDoc patName)
            ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. Pattern synonym for an '" ++ show ''Foil.AST ++ "' node of type '" ++ show conName ++ "'.")
          return
            [ PatSynSigD patName (toFreeFoilType SortTerm config outerScope innerScope rawConType)
            , PatSynD patName (PrefixPatSyn vars) ImplBidir pat
            ]

      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con  -- FIXME: params and ctx!
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

toFreeFoilClauseFrom :: Name -> FreeFoilConfig -> FreeFoilTermConfig -> Type -> Con -> Q [Clause]
toFreeFoilClauseFrom rawTypeName config termConfig@FreeFoilTermConfig{..} rawRetType = go
  where
    go = \case
      GadtC conNames rawArgTypes rawRetType' -> concat <$> do
        forM (conNames \\ [rawVarConName]) $ \conName -> do
          [(_vars, _pat, pat, exps)] <- termConToPat rawTypeName config termConfig
            (GadtC [conName] rawArgTypes rawRetType')    -- FIXME: unsafe matching!
          return [ Clause [pat] (NormalB (foldl AppE (ConE conName) exps)) [] ]

      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

toFreeFoilClauseFromBinding :: FreeFoilConfig -> FreeFoilTermConfig -> Type -> Con -> Q [Clause]
toFreeFoilClauseFromBinding config termConfig@FreeFoilTermConfig{..} rawRetType = go
  where
    go = \case
      GadtC conNames rawArgTypes rawRetType' -> concat <$> do
        forM (conNames \\ [rawVarConName]) $ \conName -> do
          [(_vars, _pat, pat, exps)] <- termConToPatBinding rawBindingName config termConfig
            (GadtC [conName] rawArgTypes rawRetType')    -- FIXME: unsafe matching!
          return [ Clause [pat] (NormalB (foldl AppE (ConE conName) exps)) [] ]

      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

toFreeFoilClauseFromQualified :: FreeFoilConfig -> Type -> Con -> Q [Clause]
toFreeFoilClauseFromQualified config rawRetType = go
  where
    go = \case
      GadtC conNames rawArgTypes rawRetType' -> concat <$> do
        forM conNames $ \conName -> do
          [(_vars, _pat, pat, exps)] <- termConToPatQualified config
            (GadtC [conName] rawArgTypes rawRetType')    -- FIXME: unsafe matching!
          return [ Clause [pat] (NormalB (foldl AppE (ConE conName) exps)) [] ]

      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)

mkFreeFoil :: FreeFoilConfig -> Q [Dec]
mkFreeFoil config@FreeFoilConfig{..} = concat <$> sequence
  [ mapM mkQuantifiedType rawQuantifiedNames
  , mapM mkBindingType freeFoilTermConfigs
  , concat <$> mapM mkSignatureTypes freeFoilTermConfigs
  , concat <$> mapM mkPatternSynonyms freeFoilTermConfigs
  ]
  where
    scope = mkName "scope"
    term = mkName "term"
    outerScope = mkName "o"
    innerScope = mkName "i"

    mkPatternSynonyms termConfig@FreeFoilTermConfig{..} = do
      ds <- mkPatternSynonyms' termConfig rawTermName
      ds' <- concat <$> mapM (mkPatternSynonyms' termConfig) rawSubTermNames
      return (ds <> ds')

    mkPatternSynonyms' FreeFoilTermConfig{..} rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      let rawRetType = PeelConT rawName (map (VarT . tvarName) tvars)
      concat <$> mapM (mkPatternSynonym rawName config FreeFoilTermConfig{..} rawRetType) cons

    mkQuantifiedType rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      let name = toFreeFoilName config rawName
          rawRetType = PeelConT rawName (map (VarT . tvarName) tvars)
          newParams = tvars ++ [PlainTV outerScope BndrReq]
          toCon = toFreeFoilCon config rawRetType (VarT outerScope) (VarT innerScope)
      newCons <- mapM toCon cons
      addModFinalizer $ putDoc (DeclDoc name)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scope-safe version of '" ++ show rawName ++ "'.")
      return (DataD [] name newParams Nothing newCons [])

    mkBindingType FreeFoilTermConfig{..} = do
      (tvars, cons) <- reifyDataOrNewtype rawBindingName
      let bindingName = toFreeFoilName config rawBindingName
          rawRetType = PeelConT rawBindingName (map (VarT . tvarName) tvars)
          newParams = tvars ++ [PlainTV outerScope BndrReq, PlainTV innerScope BndrReq]
          toCon = toFreeFoilBindingCon config rawRetType (VarT outerScope)
      newCons <- mapM toCon cons
      addModFinalizer $ putDoc (DeclDoc bindingName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A binding type, scope-safe version of '" ++ show rawBindingName ++ "'.")
      return (DataD [] bindingName newParams Nothing newCons [])

    mkSignatureTypes termConfig@FreeFoilTermConfig{..} = do
      sig <- mkSignatureType termConfig rawTermName
      subsigs <- concat <$> mapM (mkSignatureType termConfig) rawSubTermNames
      return (sig ++ subsigs)

    mkSignatureType termConfig@FreeFoilTermConfig{..} rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      let sigName = toSignatureName config rawName
          tvars' = map (VarT . tvarName) tvars
          rawRetType = PeelConT rawName tvars'
          newParams = tvars ++ [PlainTV scope BndrReq, PlainTV term BndrReq]
          toCon = toFreeFoilSigCon config termConfig sigName rawRetType (VarT scope) (VarT term)
      newCons <- catMaybes <$> mapM toCon cons
      let bindingT = PeelConT (toFreeFoilName config rawBindingName) tvars'
          sigNameT = PeelConT (toSignatureName config rawTermName) tvars'
          astName = toFreeFoilName config rawName
          scopeName = toFreeFoilScopedName config rawName
          termAST = PeelConT ''Foil.AST [bindingT, sigNameT]
          scopedTermAST = PeelConT ''Foil.ScopedAST [bindingT, sigNameT]
          n = mkName "n"
      addModFinalizer $ putDoc (DeclDoc sigName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A signature based on '" ++ show rawName ++ "'.")
      addModFinalizer $ putDoc (DeclDoc astName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scope-safe version of '" ++ show rawName ++ "'.")
      when (rawTermName == rawName) $ do
        addModFinalizer $ putDoc (DeclDoc scopeName)
          ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scoped (and scope-safe) version of '" ++ show rawName ++ "'.")
      return $ concat
        [ [ DataD [] sigName newParams Nothing newCons [DerivClause Nothing [ConT ''GHC.Generic, ConT ''Functor, ConT ''Foldable, ConT ''Traversable]] ]
        , if rawTermName == rawName
            then [ TySynD astName   tvars termAST
                 , TySynD scopeName tvars scopedTermAST ]
            else [ TySynD astName   (tvars ++ [PlainTV n BndrReq])
                    (PeelConT sigName
                      (tvars' ++
                      [ AppT scopedTermAST (VarT n)
                      , AppT termAST (VarT n) ])) ]
        ]

(-->) :: Type -> Type -> Type
a --> b = AppT (AppT ArrowT a) b

reifyDataOrNewtype :: Name -> Q ([TyVarBndr BndrVis], [Con])
reifyDataOrNewtype name = reify name >>= \case
  TyConI (DataD _ctx _name tvars _kind cons _deriv) -> return (tvars, cons)
  TyConI (NewtypeD _ctx _name tvars _kind con _deriv) -> return (tvars, [con])
  _ -> error ("not a data or newtype: " ++ show name)

mkFreeFoilConversions :: FreeFoilConfig -> Q [Dec]
mkFreeFoilConversions config@FreeFoilConfig{..} = concat <$> sequence
  [ concat <$> mapM mkConvertFrom freeFoilTermConfigs
  , concat <$> mapM mkConvertFromQuantified rawQuantifiedNames
  , concat <$> mapM mkConvertTo freeFoilTermConfigs
  ]
  where
    outerScope = mkName "o"
    innerScope = mkName "i"

    mkConvertFrom termConfig@FreeFoilTermConfig{..} = concat <$> sequence
      [ concat <$> mapM (mkConvertFromSig termConfig) (rawTermName : rawSubTermNames)
      , mkConvertFromBinding termConfig
      , mkConvertFromTerm termConfig
      , concat <$> mapM (mkConvertFromSubTerm termConfig) rawSubTermNames
      ]

    mkConvertFromSig termConfig@FreeFoilTermConfig{..} rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      let rawSigName = toSignatureName config rawName
          funName = toFreeFoilNameFrom config rawSigName
          rawRetType = PeelConT rawName (map (VarT . tvarName) tvars)
          rawTermType = PeelConT rawTermName (map (VarT . tvarName) tvars)
          rawScopedTermType = PeelConT rawScopeName (map (VarT . tvarName) tvars)
          rawBindingType = PeelConT rawBindingName (map (VarT . tvarName) tvars)
          rawScopeType = TupleT 2 `AppT` rawBindingType `AppT` rawScopedTermType
      case toFreeFoilSigType SortSubTerm config rawScopeType rawTermType rawRetType of
        Just termType -> do
          clauses <- concat <$> mapM (toFreeFoilClauseFrom rawSigName config termConfig rawRetType) cons
          addModFinalizer $ putDoc (DeclDoc funName)
            ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A helper used to convert from scope-safe to raw representation.")
          return
            [ SigD funName (AppT (AppT ArrowT termType) rawRetType)
            , FunD funName clauses ]
        Nothing -> error "impossible happened"

    mkConvertFromTerm FreeFoilTermConfig{..} = do
      (tvars, _cons) <- reifyDataOrNewtype rawTermName
      let funName = toFreeFoilNameFrom config rawTermName
          rawSigName = toSignatureName config rawTermName
          funSigName = toFreeFoilNameFrom config rawSigName
          funBindingName = toFreeFoilNameFrom config rawBindingName
          rawTermType = PeelConT rawTermName (map (VarT . tvarName) tvars)
          termType =  toFreeFoilType SortTerm config (VarT outerScope) (VarT innerScope) rawTermType
      addModFinalizer $ putDoc (DeclDoc funName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. Convert from scope-safe to raw representation.")
      return
        [ SigD funName (AppT (AppT ArrowT termType) rawTermType)
        , FunD funName [
            Clause [] (NormalB
              (VarE 'Foil.convertFromAST
                `AppE` VarE funSigName
                `AppE` VarE rawVarIdentToTermName
                `AppE` VarE funBindingName
                `AppE` VarE rawTermToScopeName
                `AppE` VarE intToRawIdentName)) []
          ]
        ]

    mkConvertFromSubTerm FreeFoilTermConfig{..} rawName = do
      (tvars, _cons) <- reifyDataOrNewtype rawName
      let funName = toFreeFoilNameFrom config rawName
          funSigName = toFreeFoilNameFrom config (toSignatureName config rawName)
          funTermName = toFreeFoilNameFrom config rawTermName
          funBindingName = toFreeFoilNameFrom config rawBindingName
          rawType = PeelConT rawName (map (VarT . tvarName) tvars)
          safeType =  toFreeFoilType SortTerm config (VarT outerScope) (VarT innerScope) rawType
      binders <- newName "binders"
      body <- newName "body"
      addModFinalizer $ putDoc (DeclDoc funName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. Convert from scope-safe to raw representation.")
      return
        [ SigD funName (AppT (AppT ArrowT safeType) rawType)
        , FunD funName [
            Clause [] (NormalB $
              InfixE
              (Just (VarE funSigName))
              (VarE '(.))
              (Just (VarE 'bimap
                `AppE` LamE [ConP 'Foil.ScopedAST [] [VarP binders, VarP body]]
                  (TupE [ Just (VarE funBindingName `AppE` VarE binders)
                        , Just (VarE rawTermToScopeName `AppE` (VarE funTermName `AppE` VarE body))])
                `AppE` VarE funTermName))) []
          ]
        ]

    mkConvertFromQuantified rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      let funName = toFreeFoilNameFrom config rawName
          rawType = PeelConT rawName (map (VarT . tvarName) tvars)
          safeType = toFreeFoilType SortTerm config (VarT outerScope) (VarT innerScope) rawType
      addModFinalizer $ putDoc (DeclDoc funName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. Convert from scope-safe to raw representation.")
      clauses <- concat <$> mapM (toFreeFoilClauseFromQualified config rawType) cons
      return
        [ SigD funName (AppT (AppT ArrowT safeType) rawType)
        , FunD funName clauses
        ]

    mkConvertFromBinding termConfig@FreeFoilTermConfig{..} = do
      (tvars, cons) <- reifyDataOrNewtype rawBindingName
      let funName = toFreeFoilNameFrom config rawBindingName
          rawRetType = PeelConT rawBindingName (map (VarT . tvarName) tvars)
          bindingType = toFreeFoilType SortBinder config (VarT outerScope) (VarT innerScope) rawRetType
      clauses <- concat <$> mapM (toFreeFoilClauseFromBinding config termConfig rawRetType) cons
      addModFinalizer $ putDoc (DeclDoc funName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. Convert a scope-safe to a raw binding.")
      return
        [ SigD funName (bindingType --> rawRetType)
        , FunD funName clauses ]

    mkConvertTo termConfig@FreeFoilTermConfig{..} = concat <$> sequence
      [ mkConvertToSig SortTerm termConfig rawTermName
      , concat <$> mapM (mkConvertToSig SortSubTerm termConfig) rawSubTermNames
      -- , mkConvertToBinding termConfig
      -- , mkConvertToTerm termConfig
      -- , concat <$> mapM (mkConvertToSubTerm termConfig) rawSubTermNames
      ]

    mkConvertToSig sort termConfig@FreeFoilTermConfig{..} rawName = do
      (tvars, cons) <- reifyDataOrNewtype rawName
      (itvars, _cons) <- reifyDataOrNewtype rawIdentName
      let rawSigName = toSignatureName config rawName
          funName = toFreeFoilNameTo config rawSigName
          rawType = PeelConT rawName (map (VarT . tvarName) tvars)
          rawIdentType = PeelConT rawIdentName (map (VarT . tvarName) (take (length itvars) tvars)) -- FIXME: undocumented hack :(
          rawTermType = PeelConT rawTermName (map (VarT . tvarName) tvars)
          rawScopedTermType = PeelConT rawScopeName (map (VarT . tvarName) tvars)
          rawBindingType = PeelConT rawBindingName (map (VarT . tvarName) tvars)
          rawScopeType = TupleT 2 `AppT` rawBindingType `AppT` rawScopedTermType
      case toFreeFoilSigType SortSubTerm config rawScopeType rawTermType rawType of
        Just safeType -> do
          let retType = case sort of
                SortTerm -> ConT ''Either `AppT` rawIdentType `AppT` safeType
                _        -> safeType
          clauses <- concat <$> mapM (sigConToClause sort rawType config termConfig) cons
          addModFinalizer $ putDoc (DeclDoc funName)
            ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A helper used to convert from raw to scope-safe representation.")
          return
            [ SigD funName (AppT (AppT ArrowT rawType) retType)
            , FunD funName clauses ]
        Nothing -> error "impossible happened"

sigConToClause :: Sort -> Type -> FreeFoilConfig -> FreeFoilTermConfig -> Con -> Q [Clause]
sigConToClause sort rawRetType config@FreeFoilConfig{..} FreeFoilTermConfig{..} = go
  where
    fromArgType :: Bool -> Name -> Type -> Q ([Pat], [Exp])
    fromArgType isVarCon theIdent = \case
      PeelConT typeName _params
        | typeName == rawIdentName, SortTerm <- sort, isVarCon -> do
            return ([VarP theIdent], [VarE theIdent])
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs -> do
            return ([], [])
        | Just _ <- lookupScopeName typeName freeFoilTermConfigs -> do
            binder <- newName "binder"
            body <- newName "body"
            return ([VarP binder, VarP body], [TupE [Just (VarE binder), Just (VarE body)]])
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameTo config rawSigName
            x <- newName "_x"
            return ([VarP x], [AppE (VarE funName) (VarE x)])
      AppT _ (PeelConT typeName _params)
        | Just _ <- lookupSubTermName typeName freeFoilTermConfigs -> do
            let rawSigName = toSignatureName config typeName
                funName = toFreeFoilNameTo config rawSigName
            x <- newName "_x"
            return ([VarP x], [AppE (AppE (VarE 'fmap) (VarE funName)) (VarE x)])
      _ -> do
        x <- newName "_x"
        return ([VarP x], [VarE x])

    go :: Con -> Q [Clause]
    go = \case
      GadtC conNames rawArgTypes _rawRetType -> concat <$> do
        theIdent <- newName "_theRawIdent"
        forM conNames $ \conName -> do
          let newConName = toSignatureName config conName
              isVarCon = conName == rawVarConName
          (concat -> pats, concat -> exps) <- unzip <$>
            mapM (fromArgType isVarCon theIdent . snd) rawArgTypes
          case sort of
            SortTerm
              | isVarCon -> return
                  [ Clause [ConP conName [] pats] (NormalB (ConE 'Left `AppE` VarE theIdent)) [] ]  -- FIXME!
              | otherwise -> return
                  [ Clause [ConP conName [] pats] (NormalB (ConE 'Right `AppE` (foldl AppE (ConE newConName) exps))) [] ]
            _ -> return
              [ Clause [ConP conName [] pats] (NormalB (foldl AppE (ConE newConName) exps)) [] ]
      NormalC conName types -> go (GadtC [conName] types rawRetType)
      RecC conName types -> go (NormalC conName (map removeName types))
      InfixC l conName r -> go (GadtC [conName] [l, r] rawRetType)
      ForallC _params _ctx con -> go con
      RecGadtC conNames argTypes retType -> go (GadtC conNames (map removeName argTypes) retType)
