{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE RankNTypes #-}
-- | Fixed examples for the generic instances of the patterns of
-- "Language.LambdaPi.Impl.FreeFoilTH".
--
-- A pattern whose raw names do not ascend arises only after sinking or
-- substitution, so the generators of the law tests reach one rarely. The
-- examples below build one directly. The last one is a shrunk
-- counterexample of the composition law of 'liftRM'.
module Language.LambdaPi.Impl.FreeFoilTHSpec (spec) where

import           Control.Monad                     (unless)
import           Test.Hspec

import           Control.Monad.Foil
import           Control.Monad.Foil.Internal       (Name (..), NameBinder (..))
import           Control.Monad.Foil.Laws           (nameBinderListNames)
import           Control.Monad.Foil.Relative       (liftRM)
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.Laws      (alphaEqNameless, showAST)
import qualified Language.LambdaPi.Impl.FreeFoilTH as TH
import           Language.LambdaPi.Impl.LawsSyntax (foilPatternNames, termSyntax)

spec :: Spec
spec = describe "generic patterns whose names do not ascend" $ do
  it "nameBinderListOf keeps the order of the pattern" $
    nameBinderListNames (nameBinderListOf (pair (var 9) (var 0))) `shouldBe` [9, 0]
  it "refreshAST keeps each binder in its position" $ do
    -- λ(x9, x0). x9
    let t = lam (pair (var 9) (var 0)) (Var (UnsafeName 9))
    refreshAST emptyScope t `alphaEquivalentTo` t
  it "liftRM into {x11, x14} agrees with liftRM through the empty scope" $ do
    -- Π(x11 : 𝕌) → λ(x9, (x11, x13)). x13
    let t = piType (var 11) universe
              (lam (pair (var 9) (pair (var 11) (var 13))) (Var (UnsafeName 13)))
    withScope [11, 14] $ \scope ->
      liftRM scope absurdName t
        `alphaEquivalentTo` liftRM scope absurdName (liftRM emptyScope absurdName t)

-- | A variable pattern that binds the raw name @x@.
var :: Int -> TH.FoilPattern n l
var x = TH.FoilPatternVar Nothing (UnsafeNameBinder (UnsafeName x))

pair :: TH.FoilPattern n i -> TH.FoilPattern i l -> TH.FoilPattern n l
pair = TH.FoilPatternPair Nothing

lam :: TH.FoilPattern n l -> TH.Term l -> TH.Term n
lam pat body = Node (TH.LamSig Nothing (ScopedAST pat body))

piType :: TH.FoilPattern n l -> TH.Term n -> TH.Term l -> TH.Term n
piType pat a body = Node (TH.PiSig Nothing a (ScopedAST pat body))

universe :: TH.Term n
universe = Node (TH.UniverseSig Nothing)

-- | A scope of exactly the given raw names, which must be distinct.
withScope :: [Int] -> (forall n. Distinct n => Scope n -> r) -> r
withScope = go emptyScope
  where
    go :: Distinct n => Scope n -> [Int] -> (forall l. Distinct l => Scope l -> r) -> r
    go scope [] k = k scope
    go scope (x : xs) k = withRefreshed scope (UnsafeName x) $ \binder ->
      go (extendScope binder scope) xs k

-- | The renaming of the empty scope. A closed term never applies it.
absurdName :: Name VoidS -> Name n
absurdName x = error ("a closed term has no free names, but x" <> show (nameId x) <> " occurs")

alphaEquivalentTo :: TH.Term n -> TH.Term n -> Expectation
alphaEquivalentTo a b = unless (alphaEqNameless foilPatternNames a b) $
  expectationFailure (showAST termSyntax a <> "\nis not α-equivalent to\n" <> showAST termSyntax b)
