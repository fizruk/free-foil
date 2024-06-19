{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.LambdaPi.Impl.FoilSpec where

import Test.Hspec
import Test.QuickCheck
import Data.Bifunctor

import qualified Control.Monad.Foil.Internal as Foil.Internal
import Control.Monad.Foil
import Language.LambdaPi.Impl.Foil

genExpr :: Distinct n => Scope n -> [Name n] -> Gen (Expr n)
genExpr scope names = go
  where
    go = oneof $
      map (pure . VarE) names ++
      [ AppE <$> go <*> go
      , do
          name <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed scope name $ \binder ->
            LamE (PatternVar binder) <$> genExpr (extendScope binder scope) (nameOf binder : map sink names)
      ]

genAlphaEquivExprs :: (Distinct n, Distinct l) => Scope n -> Scope l -> [(Name n, Name l)] -> Gen (Expr n, Expr l)
genAlphaEquivExprs scope1 scope2 names = go
  where
    go = oneof $
      map (pure . bimap VarE VarE) names ++
      [ do
          (f1, f2) <- go
          (x1, x2) <- go
          return (AppE f1 x1, AppE f2 x2)
      , do
          name1 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          name2 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed scope1 name1 $ \binder1 ->
            withRefreshed scope2 name2 $ \binder2 -> do
              let names' = (nameOf binder1, nameOf binder2) : map (bimap sink sink) names
                  scope1' = extendScope binder1 scope1
                  scope2' = extendScope binder2 scope2
              (body1, body2) <- genAlphaEquivExprs scope1' scope2' names'
              return (LamE (PatternVar binder1) body1, LamE (PatternVar binder2) body2)
      ]

instance Arbitrary (Expr VoidS) where
  arbitrary = genExpr emptyScope []

data AlphaEquivRefreshed = AlphaEquivRefreshed (Expr VoidS) (Expr VoidS)

instance Arbitrary AlphaEquivRefreshed where
  arbitrary = do
    (t, t') <- genAlphaEquivExprs emptyScope emptyScope []
    return (AlphaEquivRefreshed t t')

instance Show AlphaEquivRefreshed where
  show (AlphaEquivRefreshed t1 t2) = unlines
    [ "t1 = " <> show t1
    , "t2 = " <> show t2
    , "refreshExpr _ t1 = " <> show (refreshExpr emptyScope t1)
    , "refreshExpr _ t2 = " <> show (refreshExpr emptyScope t2)
    , "alphaEquivRefreshed _ t1 t2 = " <> show (alphaEquivRefreshed emptyScope t1 t2)
    ]

spec :: Spec
spec = do
  describe "α-equivalence" $ do
    it "alphaEquiv is correct" $ property $ forAll (genAlphaEquivExprs emptyScope emptyScope []) $ \(t, t') ->
      alphaEquiv emptyScope t t'
    it "alphaEquivRefreshed is correct" $ property $ \(AlphaEquivRefreshed t t') ->
      alphaEquivRefreshed emptyScope t t'
