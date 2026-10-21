{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
-- | 'foldAST' and 'hoistAST' on the untyped λ-calculus of
-- "Control.Monad.Free.Foil.Example". The identity transformations are
-- identities, a round trip through a sum of signatures is one, and a fold
-- into a node count counts.
module Control.Monad.Free.Foil.HoistSpec (spec) where

import           Data.Bifunctor.Sum              (Sum (..))
import           Test.Hspec

import           Control.Monad.Foil              (NameBinder, S (..))
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.Example

-- | The terms under test: Church numerals and their applications.
terms :: [(String, Expr VoidS)]
terms =
  [ ("church " ++ show n, churchN n) | n <- [0 .. 6 :: Int] ] ++
  [ ("church 2 applied to church 3", AppE (churchN 2) (churchN 3))
  , ("church 3 normalised", nf' (AppE (churchN 2) (churchN 3)))
  ]

-- | A node count, indexed by the scope so that it can be the carrier of
-- 'foldAST'.
newtype Count (n :: S) = Count { getCount :: Int }

-- | The number of variables and nodes of a term, through 'foldAST'.
sizeOf :: Expr n -> Int
sizeOf = getCount . foldAST (const (Count 1)) (\_ body -> Count (getCount body)) node
  where
    node :: ExprF (Count m) (Count m) -> Count m
    node = \case
      AppF f x -> Count (1 + getCount f + getCount x)
      LamF b   -> Count (1 + getCount b)

spec :: Spec
spec = do
  describe "hoistAST" $ do
    it "is the identity on the identity transformation" $
      mapM_ (\(name, t) -> (name, show (hoistAST id t)) `shouldBe` (name, show t)) terms
    it "round-trips through a sum of signatures" $
      let there = hoistAST L2 :: Expr n -> AST NameBinder (Sum ExprF ExprF) n
          back  = hoistAST (\case L2 x -> x; R2 x -> x)
      in mapM_ (\(name, t) -> (name, show (back (there t))) `shouldBe` (name, show t)) terms
  describe "foldAST" $ do
    it "rebuilds a term with the constructors" $
      mapM_ (\(name, t) -> (name, show (foldAST Var ScopedAST Node t)) `shouldBe` (name, show t)) terms
    it "counts the nodes of a Church numeral" $
      mapM_ (\n -> (n, sizeOf (churchN n)) `shouldBe` (n, 2 * n + 3)) [0 .. 6 :: Int]
