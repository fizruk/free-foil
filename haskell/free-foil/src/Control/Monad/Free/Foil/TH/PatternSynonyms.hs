{-# LANGUAGE LambdaCase            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults      #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns          #-}
module Control.Monad.Free.Foil.TH.PatternSynonyms where

import           Control.Monad              (forM_)
import           Control.Monad.Foil.TH.Util
import           Control.Monad.Free.Foil
import           Data.List                  (nub)
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
      (names, decs) <- unzip . concat <$> mapM (mkPatternSynonym (PeelConT signatureT (map (VarT . tvarName) params)) scope term) signatureCons
      return $ decs ++
        [ PragmaD (CompleteP ('Var : nub names) Nothing)]
    _ -> fail "cannot generate pattern synonyms"

mkPatternSynonym :: Type -> Name -> Name -> Con -> Q [(Name, Dec)]
mkPatternSynonym signatureType scope term = \case
  NormalC conName types -> mkPatternSynonym signatureType scope term
    (GadtC [conName] types (AppT (AppT signatureType (VarT scope)) (VarT term)))

  RecC conName types -> mkPatternSynonym signatureType scope term (NormalC conName (map removeName types))

  InfixC l conName r -> mkPatternSynonym signatureType scope term (NormalC conName [l, r])

  ForallC params ctx con -> do
    [ (name, PatSynSigD patName patType), patD ] <- mkPatternSynonym signatureType scope term con
    return
      [ (name, PatSynSigD patName (ForallT params ctx patType))
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
      [ [ (patternName, PatSynSigD patternName (foldr (AppT . AppT ArrowT) termType types'))
        , (patternName, PatSynD  patternName (PrefixPatSyn args) ImplBidir (ConP 'Node [] [ConP conName [] pats]))
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

    toPatternArgType i (_bang, type_@(VarT typeName))
      | typeName == scope =
          Left
            ( (mkName ("b" ++ show i), foldl AppT binderT [VarT n, VarT l])
            , (mkName ("x" ++ show i), replaceScopeTermInType l type_))
      | typeName == term =
          Right (mkName ("x" ++ show i), replaceScopeTermInType l type_)
      where
        l = mkName ("l" ++ show i)
    toPatternArgType i (_bang, type_)
      = Right (mkName ("z" ++ show i), replaceScopeTermInType l type_)
      where
        l = mkName ("l" ++ show i)

    mkPatternName conName = mkName (dropEnd (length ("Sig" :: String)) (nameBase conName))
    dropEnd k = reverse . drop k . reverse

    collapse = \case
      Left (x, y) -> [x, y]
      Right x -> [x]

    replaceScopeTermInType lscope = \case
      VarT typeName
        | typeName == scope -> PeelConT ''AST [binderT, signatureType, VarT lscope]
        | typeName == term  -> PeelConT ''AST [binderT, signatureType, VarT n]
      ForallT bndrs ctx type_ -> ForallT bndrs ctx (replaceScopeTermInType lscope type_)
      ForallVisT bndrs type_ -> ForallVisT bndrs (replaceScopeTermInType lscope type_)
      AppT f x -> AppT (replaceScopeTermInType lscope f) (replaceScopeTermInType lscope x)
      AppKindT f k -> AppKindT (replaceScopeTermInType lscope f) k
      SigT t k -> SigT (replaceScopeTermInType lscope t) k
      t@ConT{} -> t
      t@VarT{} -> t
      t@PromotedT{} -> t
      InfixT l op r -> InfixT (replaceScopeTermInType lscope l) op (replaceScopeTermInType lscope r)
      UInfixT l op r -> UInfixT (replaceScopeTermInType lscope l) op (replaceScopeTermInType lscope r)
      PromotedInfixT l op r -> PromotedInfixT (replaceScopeTermInType lscope l) op (replaceScopeTermInType lscope r)
      PromotedUInfixT l op r -> PromotedUInfixT (replaceScopeTermInType lscope l) op (replaceScopeTermInType lscope r)
      ParensT t -> ParensT (replaceScopeTermInType lscope t)
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
      ImplicitParamT s t -> ImplicitParamT s (replaceScopeTermInType lscope t)
