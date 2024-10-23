{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Free.Foil.TH.MkFreeFoil where

import           Language.Haskell.TH
import Language.Haskell.TH.Syntax (addModFinalizer)

import Data.Maybe (mapMaybe, catMaybes)
import Control.Monad (forM_)
import qualified Control.Monad.Foil as Foil
import qualified Control.Monad.Free.Foil as Foil
import           Control.Monad.Foil.TH.Util
import Data.List (find)

type NameOfIdent = Name

data FreeFoilTermConfig = FreeFoilTermConfig
  { rawIdentName    :: NameOfIdent
  , rawTermName     :: Name
  , rawBindingName  :: Name
  , rawScopeName    :: Name
  , rawVarConName   :: Name
  , rawSubTermNames :: [Name]
  }

data FreeFoilConfig = FreeFoilConfig
  { rawQuantifiedNames        :: [Name]
  , freeFoilTermConfigs       :: [FreeFoilTermConfig]
  , freeFoilNameModifier      :: String -> String
  , freeFoilScopeNameModifier :: String -> String
  , signatureNameModifier     :: String -> String
  , freeFoilConNameModifier   :: String -> String
  , ignoreNames               :: [Name]
  }

toFreeFoilName :: FreeFoilConfig -> Name -> Name
toFreeFoilName FreeFoilConfig{..} name = mkName (freeFoilNameModifier (nameBase name))

toFreeFoilScopedName :: FreeFoilConfig -> Name -> Name
toFreeFoilScopedName FreeFoilConfig{..} name = mkName (freeFoilScopeNameModifier (nameBase name))

toSignatureName :: FreeFoilConfig -> Name -> Name
toSignatureName FreeFoilConfig{..} name = mkName (signatureNameModifier (nameBase name))

toConName :: FreeFoilConfig -> Name -> Name
toConName FreeFoilConfig{..} name = mkName (freeFoilConNameModifier (nameBase name))

lookupTermName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupTermName name = find (\FreeFoilTermConfig{..} -> rawTermName == name)

lookupSubTermName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupSubTermName name = find (\FreeFoilTermConfig{..} -> name `elem` rawSubTermNames)

lookupBindingName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupBindingName name = find (\FreeFoilTermConfig{..} -> rawBindingName == name)

lookupScopeName :: Name -> [FreeFoilTermConfig] -> Maybe FreeFoilTermConfig
lookupScopeName name = find (\FreeFoilTermConfig{..} -> rawScopeName == name)

data IsBinder = ABinder | NotABinder

toFreeFoilType :: IsBinder -> FreeFoilConfig -> Type -> Type -> Type -> Type
toFreeFoilType isBinder config@FreeFoilConfig{..} outerScope innerScope = go
  where
    go = \case
      PeelConT typeName (map go -> typeParams)
        | typeName `elem` rawQuantifiedNames ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
        | typeName `elem` map rawIdentName freeFoilTermConfigs ->
            case isBinder of
              NotABinder -> PeelConT ''Foil.Name [outerScope]
              ABinder -> PeelConT ''Foil.NameBinder [outerScope, innerScope]
        | Just _ <- lookupTermName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
        | Just _ <- lookupBindingName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope, innerScope])
        | Just FreeFoilTermConfig{..} <- lookupScopeName typeName freeFoilTermConfigs ->
            PeelConT (toFreeFoilScopedName config rawTermName) (typeParams ++ [outerScope])
        | Just FreeFoilTermConfig{..} <- lookupSubTermName typeName freeFoilTermConfigs ->
            let scopeT = PeelConT (toFreeFoilScopedName config typeName) (typeParams ++ [outerScope])
                termT = PeelConT (toFreeFoilName config typeName) (typeParams ++ [outerScope])
             in PeelConT (toSignatureName config typeName) (typeParams ++ [scopeT, termT])
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

toFreeFoilSigType :: FreeFoilConfig -> Type -> Type -> Type -> Maybe Type
toFreeFoilSigType config@FreeFoilConfig{..} scope term = go
  where
    go :: Type -> Maybe Type
    go = \case
      PeelConT _typeName (mapM go -> Nothing) ->
        error "bad type params"
      PeelConT typeName (mapM go -> Just typeParams)
        | Just _ <- lookupTermName typeName freeFoilTermConfigs ->
            Just term
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
    goType = toFreeFoilType NotABinder config outerScope innerScope
    go = \case
      GadtC conNames argTypes retType -> do
        let newConNames = (map (toConName config) conNames)
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
    goType = toFreeFoilSigType config scope term
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
    goType = toFreeFoilType ABinder config theOuterScope

    goTypeArgs :: Int -> Type -> [BangType] -> Q (Type, [BangType])
    goTypeArgs _ outerScope [] = pure (outerScope, [])
    goTypeArgs i outerScope ((bang_, rawArgType) : rawArgs) = do
      case rawArgType of
        PeelConT rawTypeName _rawTypeParams
          | rawTypeName `elem` map rawIdentName (freeFoilTermConfigs config) -> do
            innerScope <- VarT <$> newName ("i" <> show i)
            let argType = toFreeFoilType ABinder config outerScope innerScope rawArgType
            (theInnerScope, argTypes) <- goTypeArgs (i + 1) innerScope rawArgs
            return (theInnerScope, ((bang_, argType) : argTypes))

          | Just _ <- lookupBindingName rawTypeName (freeFoilTermConfigs config) -> do
            innerScope <- VarT <$> newName ("i" <> show i)
            let argType = toFreeFoilType ABinder config outerScope innerScope rawArgType
            (theInnerScope, argTypes) <- goTypeArgs (i + 1) innerScope rawArgs
            return (theInnerScope, ((bang_, argType) : argTypes))

        _ -> do
          let argType = toFreeFoilType ABinder config outerScope outerScope rawArgType
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

mkFreeFoil :: FreeFoilConfig -> Q [Dec]
mkFreeFoil config@FreeFoilConfig{..} = concat <$> sequence
  [ mapM mkQuantifiedType rawQuantifiedNames
  , mapM mkBindingType freeFoilTermConfigs
  , concat <$> mapM mkSignatureTypes freeFoilTermConfigs
  ]
  where
    scope = mkName "scope"
    term = mkName "term"
    outerScope = mkName "o"
    innerScope = mkName "i"

    mkQuantifiedType rawName = do
      TyConI (DataD _ctx _name tvars _kind cons _deriv) <- reify rawName
      let name = toFreeFoilName config rawName
          rawRetType = PeelConT rawName (map (VarT . tvarName) tvars)
          newParams = tvars ++ [PlainTV outerScope BndrReq]
          toCon = toFreeFoilCon config rawRetType (VarT outerScope) (VarT innerScope)
      newCons <- mapM toCon cons
      addModFinalizer $ putDoc (DeclDoc name)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scope-safe version of '" ++ show rawName ++ "'.")
      return (DataD [] name newParams Nothing newCons [])

    mkBindingType FreeFoilTermConfig{..} = do
      TyConI (DataD _ctx _name tvars _kind cons _deriv) <- reify rawBindingName
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
      TyConI (DataD _ctx _name tvars _kind cons _deriv) <- reify rawName
      let sigName = toSignatureName config rawName
          tvars' = map (VarT . tvarName) tvars
          rawRetType = PeelConT rawName tvars'
          newParams = tvars ++ [PlainTV scope BndrReq, PlainTV term BndrReq]
          toCon = toFreeFoilSigCon config termConfig sigName rawRetType (VarT scope) (VarT term)
      newCons <- catMaybes <$> mapM toCon cons
      let bindingT = PeelConT (toFreeFoilName config rawBindingName) tvars'
          sigT = PeelConT sigName tvars'
          astName = toFreeFoilName config rawName
          scopeName = toFreeFoilScopedName config rawName
      addModFinalizer $ putDoc (DeclDoc sigName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A signature based on '" ++ show rawName ++ "'.")
      addModFinalizer $ putDoc (DeclDoc astName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scope-safe version of '" ++ show rawName ++ "'.")
      addModFinalizer $ putDoc (DeclDoc scopeName)
        ("/Generated/ with '" ++ show 'mkFreeFoil ++ "'. A scoped (and scope-safe) version of '" ++ show rawName ++ "'.")
      return
        [ DataD [] sigName newParams Nothing newCons []
        , TySynD astName   tvars (PeelConT ''Foil.AST [bindingT, sigT])
        , TySynD scopeName tvars (PeelConT ''Foil.ScopedAST [bindingT, sigT])
        ]
