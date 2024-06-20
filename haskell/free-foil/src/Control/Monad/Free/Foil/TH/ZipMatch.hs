{-# LANGUAGE LambdaCase      #-}
{-# OPTIONS_GHC -fno-warn-type-defaults      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Free.Foil.TH.ZipMatch where

import           Language.Haskell.TH

import           Control.Monad.Foil.TH.Util
import           Control.Monad.Free.Foil

-- | Generate helpful pattern synonyms given a signature bifunctor.
deriveZipMatch
  :: Name -- ^ Type name for the signature bifunctor.
  -> Q [Dec]
deriveZipMatch signatureT = do
  TyConI (DataD _ctx _name signatureTVars _kind signatureCons _deriv) <- reify signatureT

  case reverse signatureTVars of
    (tvarName -> term) : (tvarName -> scope) : (reverse -> params) -> do
      let signatureType = PeelConT signatureT (map (VarT . tvarName) params)
      clauses <- concat <$> mapM (toClause scope term) signatureCons
      let defaultClause = Clause [WildP, WildP] (NormalB (ConE 'Nothing)) []
      let instType = AppT (ConT ''ZipMatch) signatureType

      return
        [ InstanceD Nothing [] instType
          [ FunD 'zipMatch (clauses ++ [defaultClause]) ]
        ]
    _ -> fail "cannot generate pattern synonyms"

  where
    toClause :: Name -> Name -> Con -> Q [Clause]
    toClause scope term = go
      where
        go = \case
          NormalC conName types -> mkClause conName types
          RecC conName types -> go (NormalC conName (map removeName types))
          InfixC l conName r -> go (NormalC conName [l, r])
          ForallC _ _ con -> go con
          GadtC conNames types _retType -> concat <$> mapM (\conName -> mkClause conName types) conNames
          RecGadtC conNames types retType -> go (GadtC conNames (map removeName types) retType)

        mkClause :: Name -> [BangType] -> Q [Clause]
        mkClause conName types = return
          [Clause [ConP conName [] lpats, ConP conName [] rpats]
            (NormalB (AppE (ConE 'Just) (foldl AppE (ConE conName) args))) []]
          where
            (lpats, rpats, args) = unzip3
              [ case type_ of
                  VarT typeName
                    | typeName `elem` [scope, term] -> (VarP l, VarP r, TupE [Just (VarE l), Just (VarE r)])
                  _ -> (VarP l, WildP, VarE l)
              | (i, (_bang, type_)) <- zip [0..] types
              , let l = mkName ("l" ++ show i)
              , let r = mkName ("r" ++ show i)
              ]
