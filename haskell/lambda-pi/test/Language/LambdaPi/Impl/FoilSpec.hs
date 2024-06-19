{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
module Language.LambdaPi.Impl.FoilSpec where

import Test.Hspec
import Test.QuickCheck
import Data.Bifunctor

import qualified Control.Monad.Foil.Internal as Foil.Internal
import Control.Monad.Foil
import Language.LambdaPi.Impl.Foil

shrinkExprs :: (Expr n, Expr l) -> [(Expr n, Expr l)]
shrinkExprs = \case
  (AppE t1 t2, AppE t1' t2') -> [(t1, t1'), (t2, t2')]
  (LamE x body, LamE x' body') ->
    [ (LamE x t, LamE x' t')
    | (t, t') <- shrinkExprs (body, body')]
  _ -> []

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

genAlphaEquivExprs
  :: (Distinct n, Distinct l)
  => (forall x y r. Distinct x => Scope x -> Name y -> (forall o'. DExt x o' => NameBinder x o' -> r) -> r)
  -> Scope n -> Scope l -> [(Name n, Name l)] -> Gen (Expr n, Expr l)
genAlphaEquivExprs withRefreshed' scope1 scope2 names = sized go
  where
    go n = oneof $
      map (pure . bimap VarE VarE) names ++ concat
      [ if n < 1 then [] else [ do
          (f1, f2) <- go (n `div` 2)
          (x1, x2) <- go (n `div` 2)
          return (AppE f1 x1, AppE f2 x2)
        ]
        -- allow LamE when we do not have any names
      , if n < 1 && not (null names) then [] else [ do
          name1 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          name2 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed' scope1 name1 $ \binder1 ->
            withRefreshed' scope2 name2 $ \binder2 -> do
              let names' = (nameOf binder1, nameOf binder2) : map (bimap sink sink) names
                  scope1' = extendScope binder1 scope1
                  scope2' = extendScope binder2 scope2
              (body1, body2) <- resize (max 0 (n - 1)) $ genAlphaEquivExprs withRefreshed' scope1' scope2' names'
              return (LamE (PatternVar binder1) body1, LamE (PatternVar binder2) body2)
        ]
      ]

-- | Alter at most @n@ names in a given expression.
-- The result contains the number of unused changes and a new expression.
-- If the result contains the original number, then no changes took place.
alterNames :: Distinct n => Scope n -> [Name n] -> Int -> Expr n -> Gen (Int, Expr n)
alterNames scope names = go
  where
    go n = \case
      t@(VarE x) -> elements $
        (n, t) : if n > 0 then [ (n - 1, VarE name) | name <- names, name /= x ] else []
      AppE l r -> do
        (m, l') <- go n l
        (k, r') <- go m r
        return (k, AppE l' r')
      LamE x body ->
        case (assertExtPattern x, assertDistinctPattern x) of
          (Ext, Distinct) -> fmap (LamE x) <$>
            alterNames (extendScopePattern x scope) (namesOfPattern x ++ map sink names) n body
      PiE x a b ->
        case (assertExtPattern x, assertDistinctPattern x) of
          (Ext, Distinct) -> do
            (m, a') <- go n a
            (k, b') <- alterNames (extendScopePattern x scope) (namesOfPattern x ++ map sink names) m b
            return (k, PiE x a' b')
      PairE l r -> do
        (m, l') <- go n l
        (k, r') <- go m r
        return (k, PairE l' r')
      FirstE t -> fmap FirstE <$> go n t
      SecondE t -> fmap SecondE <$> go n t
      ProductE l r -> do
        (m, l') <- go n l
        (k, r') <- go m r
        return (k, ProductE l' r')
      UniverseE -> pure (n, UniverseE)

instance Arbitrary (Expr VoidS) where
  arbitrary = genExpr emptyScope []

data AlphaEquiv = AlphaEquiv Bool (Expr VoidS) (Expr VoidS)

instance Show AlphaEquiv where
  show (AlphaEquiv equiv t1 t2) = unlines
    [ "t1 = " <> show t1
    , "t2 = " <> show t2
    , if equiv
        then "t1 and t2 are α-equivalent"
        else "t1 and t2 are not α-equivalent"
    ]

instance Arbitrary AlphaEquiv where
  arbitrary = do
    (t, t') <- genAlphaEquivExprs withRefreshed emptyScope emptyScope []
    (n, alt) <- alterNames emptyScope [] 1 t
    return (AlphaEquiv (n == 1) alt t')

  -- cannot shrink non-equivalent pair
  -- since we do not know which subterm contains non-equivalent part
  shrink (AlphaEquiv False _ _) = []
  -- if terms are equivalent, then we can shrink
  shrink (AlphaEquiv True t t') =
    [ AlphaEquiv True s s'
    | (s, s') <- shrinkExprs (t, t')
    ]

newtype AlphaEquivRefreshed = AlphaEquivRefreshed AlphaEquiv
  deriving (Arbitrary)

instance Show AlphaEquivRefreshed where
  show (AlphaEquivRefreshed ae@(AlphaEquiv _equiv t1 t2)) = unlines
    [  show ae
    , "refreshExpr _ t1 = " <> show (refreshExpr emptyScope t1)
    , "refreshExpr _ t2 = " <> show (refreshExpr emptyScope t2)
    , "alphaEquivRefreshed _ t1 t2 = " <> show (alphaEquivRefreshed emptyScope t1 t2)
    ]

genExprWithFresh :: (Distinct n, Distinct l) => Scope n -> Scope l -> [(Name n, Name l)] -> Gen (Expr n, Expr l)
genExprWithFresh = genAlphaEquivExprs (\s _ -> withFresh s)

data ExprWithFresh = ExprWithFresh (Expr VoidS) (Expr VoidS)

instance Arbitrary ExprWithFresh where
  arbitrary = do
    (t, t') <- genExprWithFresh emptyScope emptyScope []
    return (ExprWithFresh t t')
  shrink (ExprWithFresh t t') =
    [ ExprWithFresh s s'
    | (s, s') <- shrinkExprs (t, t')
    ]

instance Show ExprWithFresh where
  show (ExprWithFresh t t') = unlines
    [ "              t = " <> show t
    , "        fresh t = " <> show t'
    , "refreshExpr _ t = " <> show (refreshExpr emptyScope t)
    ]

spec :: Spec
spec = do
  describe "α-equivalence" $ do
    it "refreshExpr is correct" $ property $ \(ExprWithFresh t t') ->
      refreshExpr emptyScope t `unsafeEqExpr` t'
    it "alphaEquiv is correct" $ property $ \(AlphaEquiv equiv t t') ->
      alphaEquiv emptyScope t t' `shouldBe` equiv
    it "alphaEquivRefreshed is correct" $ property $ \(AlphaEquivRefreshed (AlphaEquiv equiv t t')) ->
      alphaEquivRefreshed emptyScope t t' `shouldBe` equiv
