{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.LambdaPi.Impl.FreeFoilSpec where

import Control.Monad.State
import Test.Hspec
import Test.QuickCheck
import Data.Bifunctor
import Data.Bitraversable

import qualified Control.Monad.Foil.Internal as Foil.Internal
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Language.LambdaPi.Impl.FreeFoil

shrinkLambdaPis :: (LambdaPi n, LambdaPi l) -> [(LambdaPi n, LambdaPi l)]
shrinkLambdaPis = \case
  (App t1 t2, App t1' t2') -> [(t1, t1'), (t2, t2')]
  (Pair t1 t2, Pair t1' t2') -> [(t1, t1'), (t2, t2')]
  (First t, First t') -> [(t, t')]
  (Second t, Second t') -> [(t, t')]
  (Product t1 t2, Product t1' t2') -> [(t1, t1'), (t2, t2')]
  (Lam x body, Lam x' body') ->
    [ (Lam x t, Lam x' t')
    | (t, t') <- shrinkLambdaPis (body, body')]
  (Pi x a b, Pi x' a' b') ->
    [ (Pi x c d, Pi x' c' d')
    | (c, c') <- shrinkLambdaPis (a, a')
    , (d, d') <- shrinkLambdaPis (b, b')]
  _ -> []

genLambdaPi :: Distinct n => Scope n -> [Name n] -> Gen (LambdaPi n)
genLambdaPi scope names = fst <$> genAlphaEquivLambdaPis withRefreshed scope scope (zip names names)

genAlphaEquivLambdaPis
  :: (Distinct n, Distinct l)
  => (forall x y r. Distinct x => Scope x -> Name y -> (forall o'. DExt x o' => NameBinder x o' -> r) -> r)
  -> Scope n -> Scope l -> [(Name n, Name l)] -> Gen (LambdaPi n, LambdaPi l)
genAlphaEquivLambdaPis withRefreshed' scope1 scope2 names = sized go
  where
    go n = oneof $
      map (pure . bimap Var Var) names ++ concat
      [ if n < 1 then [] else [ do
          (f1, f2) <- go (n `div` 2)
          (x1, x2) <- go (n `div` 2)
          return (App f1 x1, App f2 x2)
        , do
          (f1, f2) <- go (n `div` 2)
          (x1, x2) <- go (n `div` 2)
          return (Pair f1 x1, Pair f2 x2)
        , bimap First First <$> go (n - 1)
        , bimap Second Second <$> go (n - 1)
        , do
          (f1, f2) <- go (n `div` 2)
          (x1, x2) <- go (n `div` 2)
          return (Product f1 x1, Product f2 x2)
        , pure (Universe, Universe)
        , do
          name1 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          name2 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed' scope1 name1 $ \binder1 ->
            withRefreshed' scope2 name2 $ \binder2 -> do
              let names' = (nameOf binder1, nameOf binder2) : map (bimap sink sink) names
                  scope1' = extendScope binder1 scope1
                  scope2' = extendScope binder2 scope2
              (a1, a2) <- go (n `div` 2)
              (body1, body2) <- resize (n `div` 2) $ genAlphaEquivLambdaPis withRefreshed' scope1' scope2' names'
              return (Pi binder1 a1 body1, Pi binder2 a2 body2)
        ]
      , if n < 1 && not (null names) then [] else [ do
          name1 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          name2 <- Foil.Internal.UnsafeName <$> choose (1, 1000)
          withRefreshed' scope1 name1 $ \binder1 ->
            withRefreshed' scope2 name2 $ \binder2 -> do
              let names' = (nameOf binder1, nameOf binder2) : map (bimap sink sink) names
                  scope1' = extendScope binder1 scope1
                  scope2' = extendScope binder2 scope2
              (body1, body2) <- resize (max 0 (n - 1)) $ genAlphaEquivLambdaPis withRefreshed' scope1' scope2' names'
              return (Lam binder1 body1, Lam binder2 body2)
        ]
      ]

-- | Alter at most @n@ names in a given expression.
-- The result contains the number of unused changes and a new expression.
-- If the result contains the original number, then no changes took place.
alterNames :: Distinct n => Scope n -> [Name n] -> LambdaPi n -> StateT Int Gen (LambdaPi n)
alterNames scope names = go
  where
    go = \case
      t@(Var x) -> do
        n <- get
        (m, t') <- lift $ elements $
          (n, t) : if n > 0 then [ (n - 1, Var name) | name <- names, name /= x ] else []
        put m
        return t'
      Node node -> Node <$> bitraverse goScoped go node

    goScoped (ScopedAST binder body) =
      case (assertExt binder, assertDistinct binder) of
        (Ext, Distinct) -> ScopedAST binder <$>
          alterNames (extendScope binder scope) (nameOf binder : map sink names) body

instance Arbitrary (LambdaPi VoidS) where
  arbitrary = genLambdaPi emptyScope []

data AlphaEquiv = AlphaEquiv Bool (LambdaPi VoidS) (LambdaPi VoidS)

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
    (t, t') <- genAlphaEquivLambdaPis withRefreshed emptyScope emptyScope []
    (alt, n) <- runStateT (alterNames emptyScope [] t) 1
    return (AlphaEquiv (n == 1) alt t')

  -- cannot shrink non-equivalent pair
  -- since we do not know which subterm contains non-equivalent part
  shrink (AlphaEquiv False _ _) = []
  -- if terms are equivalent, then we can shrink
  shrink (AlphaEquiv True t t') =
    [ AlphaEquiv True s s'
    | (s, s') <- shrinkLambdaPis (t, t')
    ]

newtype AlphaEquivRefreshed = AlphaEquivRefreshed AlphaEquiv
  deriving (Arbitrary)

instance Show AlphaEquivRefreshed where
  show (AlphaEquivRefreshed ae@(AlphaEquiv _equiv t1 t2)) = unlines
    [ show ae
    , "refreshAST _ t1 = " <> show (refreshAST emptyScope t1)
    , "refreshAST _ t2 = " <> show (refreshAST emptyScope t2)
    , "alphaEquivRefreshed _ t1 t2 = " <> show (alphaEquivRefreshed emptyScope t1 t2)
    ]

data LambdaPiWithFresh = LambdaPiWithFresh (LambdaPi VoidS) (LambdaPi VoidS)

instance Arbitrary LambdaPiWithFresh where
  arbitrary = do
    (t, t') <- genAlphaEquivLambdaPis (\s _ -> withFresh s) emptyScope emptyScope []
    return (LambdaPiWithFresh t t')

  shrink (LambdaPiWithFresh t t') =
    [ LambdaPiWithFresh s s'
    | (s, s') <- shrinkLambdaPis (t, t')
    ]

instance Show LambdaPiWithFresh where
  show (LambdaPiWithFresh t t') = unlines
    [ "             t = " <> show t
    , "       fresh t = " <> show t'
    , "refreshAST _ t = " <> show (refreshAST emptyScope t)
    ]

spec :: Spec
spec = do
  describe "α-equivalence" $ do
    it "refreshAST is correct" $ property $ \(LambdaPiWithFresh t t') ->
      refreshAST emptyScope t `unsafeEqAST` t'
    it "alphaEquiv is correct" $ property $ \(AlphaEquiv equiv t t') ->
      alphaEquiv emptyScope t t' `shouldBe` equiv
    it "alphaEquivRefreshed is correct" $ property $ \(AlphaEquivRefreshed (AlphaEquiv equiv t t')) ->
      alphaEquivRefreshed emptyScope t t' `shouldBe` equiv
