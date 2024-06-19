{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.LambdaPi.Impl.FreeFoilSpec where

import Test.Hspec
import Test.QuickCheck
import Data.Bifunctor

import qualified Control.Monad.Foil.Internal as Foil.Internal
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Language.LambdaPi.Impl.FreeFoil

genLambdaPi :: Distinct n => Scope n -> [Name n] -> Gen (LambdaPi n)
genLambdaPi scope names = go
  where
    go = oneof $
      map (pure . Var) names ++
      [ App <$> go <*> go
      , do
          name <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed scope name $ \binder ->
            Lam binder <$> genLambdaPi (extendScope binder scope) (nameOf binder : map sink names)
      ]

genAlphaEquivLambdaPis :: (Distinct n, Distinct l) => Scope n -> Scope l -> [(Name n, Name l)] -> Gen (LambdaPi n, LambdaPi l)
genAlphaEquivLambdaPis scope1 scope2 names = go
  where
    go = oneof $
      map (pure . bimap Var Var) names ++
      [ do
          (f1, f2) <- go
          (x1, x2) <- go
          return (App f1 x1, App f2 x2)
      , do
          name1 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          name2 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed scope1 name1 $ \binder1 ->
            withRefreshed scope2 name2 $ \binder2 -> do
              let names' = (nameOf binder1, nameOf binder2) : map (bimap sink sink) names
                  scope1' = extendScope binder1 scope1
                  scope2' = extendScope binder2 scope2
              (body1, body2) <- genAlphaEquivLambdaPis scope1' scope2' names'
              return (Lam binder1 body1, Lam binder2 body2)
      ]

instance Arbitrary (LambdaPi VoidS) where
  arbitrary = genLambdaPi emptyScope []

data AlphaEquivRefreshed = AlphaEquivRefreshed (LambdaPi VoidS) (LambdaPi VoidS)

instance Arbitrary AlphaEquivRefreshed where
  arbitrary = do
    (t, t') <- genAlphaEquivLambdaPis emptyScope emptyScope []
    return (AlphaEquivRefreshed t t')

instance Show AlphaEquivRefreshed where
  show (AlphaEquivRefreshed t1 t2) = unlines
    [ "t1 = " <> show t1
    , "t2 = " <> show t2
    , "refreshAST _ t1 = " <> show (refreshAST emptyScope t1)
    , "refreshAST _ t2 = " <> show (refreshAST emptyScope t2)
    , "alphaEquivRefreshed _ t1 t2 = " <> show (alphaEquivRefreshed emptyScope t1 t2)
    ]

spec :: Spec
spec = do
  describe "α-equivalence" $ do
    it "alphaEquiv is correct" $ property $ forAll (genAlphaEquivLambdaPis emptyScope emptyScope []) $ \(t, t') ->
      alphaEquiv emptyScope t t'
    it "alphaEquivRefreshed is correct" $ property $ \(AlphaEquivRefreshed t t') ->
      alphaEquivRefreshed emptyScope t t'
