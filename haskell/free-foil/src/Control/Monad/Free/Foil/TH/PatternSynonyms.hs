{-# LANGUAGE LambdaCase      #-}
{-# OPTIONS_GHC -fno-warn-type-defaults      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
module Control.Monad.Free.Foil.TH.PatternSynonyms where

import           Control.Monad              (forM_)
import           Control.Monad.Foil.TH.Util
import           Control.Monad.Free.Foil
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

-- | Generate helpful pattern synonyms given a signature bifunctor.
mkPatternSynonyms
  :: Name -- ^ Type name for the signature bifunctor.
  -> Q [Dec]
mkPatternSynonyms signatureT = do
  TyConI (DataD _ctx _name signatureTVars _kind signatureCons _deriv) <- reify signatureT

  case reverse signatureTVars of
    (tvarName -> term) : (tvarName -> scope) : (reverse -> params) -> do
      concat <$> mapM (mkPatternSynonym (PeelConT signatureT (map (VarT . tvarName) params)) scope term) signatureCons
    _ -> fail "cannot generate pattern synonyms"

mkPatternSynonym :: Type -> Name -> Name -> Con -> Q [Dec]
mkPatternSynonym signatureType scope term = \case
  NormalC conName types -> mkPatternSynonym signatureType scope term
    (GadtC [conName] types (AppT (AppT signatureType (VarT scope)) (VarT term)))

  RecC conName types -> mkPatternSynonym signatureType scope term (NormalC conName (map removeName types))

  InfixC l conName r -> mkPatternSynonym signatureType scope term (NormalC conName [l, r])

  ForallC params ctx con -> do
    [ PatSynSigD patName patType, patD ] <- mkPatternSynonym signatureType scope term con
    return
      [ PatSynSigD patName (ForallT params ctx patType)
      , patD
      ]

  GadtC conNames types _retType -> do
    let argsWithTypes = zipWith toPatternArgType [0..] types
        argsWithTypes' = foldMap collapse argsWithTypes
        pats   = map toArg argsWithTypes
        args  = map fst argsWithTypes'
        types' = map snd argsWithTypes'
    forM_ conNames $ \conName ->
      addModFinalizer $ putDoc (DeclDoc (mkPatternName conName))
        ("/Generated/ with '" ++ show 'mkPatternSynonyms ++ "'. Pattern synonym for an '" ++ show ''AST ++ "' node of type '" ++ show conName ++ "'.")
    return $ concat
      [ [ PatSynSigD patternName (foldr (AppT . AppT ArrowT) termType types')
        , PatSynD  patternName (PrefixPatSyn args) ImplBidir (ConP 'Node [] [ConP conName [] pats])
        ]
      | conName <- conNames
      , let patternName = mkPatternName conName
      ]

  RecGadtC conNames types retType -> mkPatternSynonym signatureType scope term (GadtC conNames (map removeName types) retType)

  where
    n = mkName "n"
    binderT = VarT (mkName "binder")
    termType = PeelConT ''AST [binderT, signatureType, VarT n]
    toArg = \case
      Left ((b, _), (x, _)) -> ConP 'ScopedAST [] [VarP b, VarP x]
      Right (x, _) -> VarP x

    toPatternArgType i (_bang, VarT typeName)
      | typeName == scope =
          Left
            ( (mkName ("b" ++ show i), foldl AppT binderT [VarT n, VarT l])
            , (mkName ("x" ++ show i), PeelConT ''AST [binderT, signatureType, VarT l]))
      | typeName == term =
          Right (mkName ("x" ++ show i), PeelConT ''AST [binderT, signatureType, VarT n])
      where
        l = mkName ("l" ++ show i)
    toPatternArgType i (_bang, type_)
      = Right (mkName ("z" ++ show i), type_)

    mkPatternName conName = mkName (dropEnd (length "Sig") (nameBase conName))
    dropEnd k = reverse . drop k . reverse

    collapse = \case
      Left (x, y) -> [x, y]
      Right x -> [x]
