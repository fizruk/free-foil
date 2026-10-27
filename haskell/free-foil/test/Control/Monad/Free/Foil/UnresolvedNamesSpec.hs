{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

-- | 'unresolvedNames' and 'unresolvedNamesWith' on a small raw λ-calculus,
-- against what 'tryConvertToASTWith' reports.
module Control.Monad.Free.Foil.UnresolvedNamesSpec (spec) where

import           Data.Bifunctor.TH
import           Data.Map                (Map)
import qualified Data.Map                as Map
import           Test.Hspec

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil
import           Data.ZipMatchK.TH       (deriveZipMatchK)

data LamSig scope term
  = App term term
  | Lam scope
  deriving (Functor, Foldable, Traversable)

deriveBifunctor ''LamSig
deriveBifoldable ''LamSig
deriveBitraversable ''LamSig
deriveZipMatchK ''LamSig

type Term = AST Foil.NameBinder LamSig

data Raw = RVar String | RApp Raw Raw | RLam String Raw

toSig :: Raw -> Either String (LamSig (String, Raw) Raw)
toSig = \case
  RVar x   -> Left x
  RApp f a -> Right (App f a)
  RLam x b -> Right (Lam (x, b))

fromRawPattern
  :: Foil.Distinct n
  => Foil.Scope n
  -> Map String (Foil.Name n)
  -> String
  -> (forall l. Foil.DExt n l => Foil.NameBinder n l -> Map String (Foil.Name l) -> r)
  -> r
fromRawPattern scope names x cont = Foil.withFresh scope $ \binder ->
  cont binder (Map.insert x (Foil.nameOf binder) (fmap Foil.sink names))

-- | The constant @c@, which stands for λy. y.
constants :: Map String (Term Foil.VoidS)
constants = Map.singleton "c" $ Foil.withFresh Foil.emptyScope $ \y ->
  Node (Lam (ScopedAST y (Var (Foil.nameOf y))))

-- | c (λx. x d)
raw :: Raw
raw = RApp (RVar "c") (RLam "x" (RApp (RVar "x") (RVar "d")))

spec :: Spec
spec = do
  describe "unresolvedNames" $
    it "reports a constant as unresolved" $
      unresolvedNames toSig fromRawPattern id Foil.emptyScope Map.empty raw
        `shouldBe` [UnresolvedName "c" [], UnresolvedName "d" ["x"]]

  describe "unresolvedNamesWith" $ do
    it "resolves the constants" $
      unresolvedNamesWith toSig fromRawPattern id Foil.emptyScope Map.empty constants raw
        `shouldBe` [UnresolvedName "d" ["x", "c"]]
    it "reports first what tryConvertToASTWith reports" $
      either Just (const Nothing)
        (tryConvertToASTWith toSig fromRawPattern id Foil.emptyScope Map.empty constants raw)
        `shouldBe` Just (UnresolvedName "d" ["x", "c"])
