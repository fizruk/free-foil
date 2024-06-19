{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Free.Foil.TH.Signature where

import           Language.Haskell.TH

import Control.Monad.Foil.TH.Util
import Data.Maybe (catMaybes)

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

  return
    [ DataD [] signatureT (termTVars ++ [PlainTV scope BndrReq, PlainTV term BndrReq]) Nothing signatureCons []
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

      NormalC conName params -> Just . NormalC conName' . catMaybes <$> mapM toSignatureParam params
        where
          conName' = mkName (nameBase conName ++ "Sig")
      RecC conName params -> Just . RecC conName' . catMaybes <$> mapM toSignatureParam' params
        where
          conName' = mkName (nameBase conName ++ "Sig")
      InfixC l conName r -> Just <$> (flip InfixC conName' <$> toInfixParam l <*> toInfixParam r)
        where
          conName' = mkName (nameBase conName ++ "---")
      ForallC params ctx con -> fmap (ForallC params ctx) <$> toSignatureCons scope term con
      GadtC params argTypes retType -> Just <$> (GadtC params <$> (catMaybes <$> mapM toSignatureParam argTypes) <*> retType')
        where
          retType' = case retType of
            PeelConT typeName typeParams
              | typeName == termT -> return (PeelConT signatureT (typeParams ++ [VarT scope, VarT term]))
            _ -> fail "unexpected return type in a GADT constructor"
      RecGadtC params argTypes retType -> Just <$> (RecGadtC params <$> (catMaybes <$> mapM toSignatureParam' argTypes) <*> retType')
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

        toSignatureParam (bang_, PeelConT typeName _typeParams)
          | typeName == nameT = fail ("variable with other stuff in constructor: " ++ show con')
          | typeName == patternT = pure Nothing -- skip binders, they will be inserted automatically with each scoped term
          | typeName == scopeT = pure (Just (bang_, VarT scope))
          | typeName == termT = pure (Just (bang_, VarT term))
        toSignatureParam bt = pure (Just bt)  -- everything else remains as is
