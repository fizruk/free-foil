{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Free.Foil.TH.Signature where

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import           Control.Monad              (forM_)
import           Control.Monad.Foil.TH.Util
import           Data.Maybe                 (catMaybes)

-- | Generate a signature for the free foil (or free scoped monads)
-- based on a naïve recursive abstract syntax representation,
-- with clearly separated types for terms, variable identifiers, scoped terms,
-- and patterns (binders).
mkSignature
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkSignature termT nameT scopeT patternT = do
  scope <- newName "scope"
  term <- newName "term"
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT

  signatureCons <- catMaybes <$> mapM (toSignatureCons scope term) termCons

  addModFinalizer $ putDoc (DeclDoc signatureT)
    ("/Generated/ with '" ++ show 'mkSignature ++ "'. A signature bifunctor, specifying the nodes of a syntax tree corresponding to '" ++ show termT ++ "'.")
  return
    [ DataD [] signatureT (termTVars ++ [PlainTV scope BndrReq, PlainTV term BndrReq]) Nothing signatureCons
      [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]
    ]
  where
    signatureT = mkName (nameBase termT ++ "Sig")

    toSignatureCons :: Name -> Name -> Con -> Q (Maybe Con)
    toSignatureCons scope term con' = case con' of
      -- treat constructors with a single variable field as variable constructor and ignore
      NormalC _conName types | or [ typeName == nameT | (_bang, PeelConT typeName _typeParams) <- types ]
        -> pure Nothing
      RecC _conName types | or [ typeName == nameT | (_name, _bang, PeelConT typeName _typeParams) <- types ]
        -> pure Nothing

      NormalC conName params -> do
        addModFinalizer $ putDoc (DeclDoc conName') ("Corresponds to '" ++ show conName ++ "'.")
        Just . NormalC conName' . catMaybes <$> mapM toSignatureParam params
        where
          conName' = mkName (nameBase conName ++ "Sig")
      RecC conName params -> do
        addModFinalizer $ putDoc (DeclDoc conName') ("Corresponds to '" ++ show conName ++ "'.")
        Just . RecC conName' . catMaybes <$> mapM toSignatureParam' params
        where
          conName' = mkName (nameBase conName ++ "Sig")
      InfixC l conName r -> do
        addModFinalizer $ putDoc (DeclDoc conName') ("Corresponds to '" ++ show conName ++ "'.")
        Just <$> (flip InfixC conName' <$> toInfixParam l <*> toInfixParam r)
        where
          conName' = mkName (nameBase conName ++ "---")
      ForallC params ctx con -> fmap (ForallC params ctx) <$> toSignatureCons scope term con
      GadtC conNames argTypes retType -> do
        let conNames' = map (\conName -> mkName (nameBase conName ++ "---")) conNames
        forM_ (zip conNames conNames') $ \(conName, conName') ->
          addModFinalizer $ putDoc (DeclDoc conName') ("Corresponds to '" ++ show conName ++ "'.")
        Just <$> (GadtC conNames' <$> (catMaybes <$> mapM toSignatureParam argTypes) <*> retType')
        where
          retType' = case retType of
            PeelConT typeName typeParams
              | typeName == termT -> return (PeelConT signatureT (typeParams ++ [VarT scope, VarT term]))
            _ -> fail "unexpected return type in a GADT constructor"
      RecGadtC conNames argTypes retType -> do
        let conNames' = map (\conName -> mkName (nameBase conName ++ "---")) conNames
        forM_ (zip conNames conNames') $ \(conName, conName') ->
          addModFinalizer $ putDoc (DeclDoc conName') ("Corresponds to '" ++ show conName ++ "'.")
        Just <$> (RecGadtC conNames' <$> (catMaybes <$> mapM toSignatureParam' argTypes) <*> retType')
        where
          retType' = case retType of
            PeelConT typeName typeParams
              | typeName == termT -> return (PeelConT signatureT (typeParams ++ [VarT scope, VarT term]))
            _ -> fail "unexpected return type in a GADT constructor"

      where
        toInfixParam (bang_, type_) = toSignatureParam (bang_, type_) >>= \case
          Nothing -> pure (bang_, VarT ''())
          Just bt -> pure bt

        toSignatureParam' (name, bang_, type_) = fmap k <$> toSignatureParam (bang_, type_)
          where
            k (x, y) = (name, x, y)

        toSignatureParam (_bang, PeelConT typeName _typeParams)
          | typeName == nameT = fail ("variable with other stuff in constructor: " ++ show con')
          | typeName == patternT = pure Nothing -- skip binders, they will be inserted automatically with each scoped term
        toSignatureParam (bang_, type_) = pure (Just (bang_, replaceScopeTermInType type_))

        replaceScopeTermInType = \case
          PeelConT typeName _typeParams
            | typeName == scopeT -> VarT scope
            | typeName == termT -> VarT term
          ForallT bndrs ctx type_ -> ForallT bndrs ctx (replaceScopeTermInType type_)
          ForallVisT bndrs type_ -> ForallVisT bndrs (replaceScopeTermInType type_)
          AppT f x -> AppT (replaceScopeTermInType f) (replaceScopeTermInType x)
          AppKindT f k -> AppKindT (replaceScopeTermInType f) k
          SigT t k -> SigT (replaceScopeTermInType t) k
          t@ConT{} -> t
          t@VarT{} -> t
          t@PromotedT{} -> t
          InfixT l op r -> InfixT (replaceScopeTermInType l) op (replaceScopeTermInType r)
          UInfixT l op r -> UInfixT (replaceScopeTermInType l) op (replaceScopeTermInType r)
          PromotedInfixT l op r -> PromotedInfixT (replaceScopeTermInType l) op (replaceScopeTermInType r)
          PromotedUInfixT l op r -> PromotedUInfixT (replaceScopeTermInType l) op (replaceScopeTermInType r)
          ParensT t -> ParensT (replaceScopeTermInType t)
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
          ImplicitParamT s t -> ImplicitParamT s (replaceScopeTermInType t)
