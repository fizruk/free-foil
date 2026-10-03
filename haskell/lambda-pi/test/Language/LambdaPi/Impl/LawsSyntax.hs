{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
-- | The λΠ-calculus, made ready for the law tests of
-- "Control.Monad.Foil.Laws" and "Control.Monad.Free.Foil.Laws": the
-- 'SyntaxGen' of the free foil implementations, and generators of the
-- patterns of "Language.LambdaPi.Impl.FreeFoilTH".
module Language.LambdaPi.Impl.LawsSyntax (
  -- * "Language.LambdaPi.Impl.FreeFoil"
  lambdaPiSyntax,
  -- * "Language.LambdaPi.Impl.FreeFoilTH"
  termSyntax,
  genFoilPattern,
  genFoilPatternPair,
  foilPatternNames,
  showTermNode,
) where

import           Data.Bifunctor.Sum                 (Sum (..))
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Laws
import           Language.LambdaPi.Impl.FreeFoil    (LambdaPiF (..), PairF (..))
import qualified Language.LambdaPi.Impl.FreeFoilTH  as TH
import qualified Language.LambdaPi.Syntax.Abs       as Raw

-- * "Language.LambdaPi.Impl.FreeFoil"

-- | λΠ with pairs, with a single binder per scoped term.
lambdaPiSyntax :: SyntaxGen NameBinder (Sum LambdaPiF PairF)
lambdaPiSyntax = SyntaxGen
  { sgShapes =
      [ L2 (AppF () ()), L2 (LamF ()), L2 (PiF () ()), L2 UniverseF
      , R2 (PairF () ()), R2 (FirstF ()), R2 (SecondF ()), R2 (ProductF () ()) ]
  , sgPattern = genNameBinder
  , sgPatternNames = nameBinderNames
  , sgShowNode = \case
      L2 (AppF f x)     -> "(" <> f <> " " <> x <> ")"
      L2 (LamF body)    -> body
      L2 (PiF a body)   -> "Π(" <> a <> ") " <> body
      L2 UniverseF      -> "𝕌"
      R2 (PairF l r)    -> "(" <> l <> ", " <> r <> ")"
      R2 (FirstF t)     -> "π₁(" <> t <> ")"
      R2 (SecondF t)    -> "π₂(" <> t <> ")"
      R2 (ProductF l r) -> "(" <> l <> " × " <> r <> ")"
  }

-- * "Language.LambdaPi.Impl.FreeFoilTH"

-- | The generated λΠ, with patterns that are wildcards, variables and
-- pairs. Locations are 'Nothing' throughout.
termSyntax :: SyntaxGen TH.FoilPattern (TH.Term'Sig Raw.BNFC'Position)
termSyntax = SyntaxGen
  { sgShapes =
      [ TH.AppSig loc () (), TH.LamSig loc (), TH.PiSig loc () (), TH.UniverseSig loc
      , TH.PairSig loc () (), TH.FirstSig loc (), TH.SecondSig loc (), TH.ProductSig loc () () ]
  , sgPattern = genFoilPattern
  , sgPatternNames = foilPatternNames
  , sgShowNode = showTermNode
  }
  where
    loc = Nothing

-- | Print a node of the generated signature.
showTermNode :: TH.Term'Sig a String String -> String
showTermNode = \case
  TH.AppSig _ f x     -> "(" <> f <> " " <> x <> ")"
  TH.LamSig _ body    -> body
  TH.PiSig _ a body   -> "Π(" <> a <> ") " <> body
  TH.UniverseSig _    -> "𝕌"
  TH.PairSig _ l r    -> "(" <> l <> ", " <> r <> ")"
  TH.FirstSig _ t     -> "π₁(" <> t <> ")"
  TH.SecondSig _ t    -> "π₂(" <> t <> ")"
  TH.ProductSig _ l r -> "(" <> l <> " × " <> r <> ")"

-- | The names a generated pattern binds, left to right.
foilPatternNames :: PatternNames (TH.FoilPattern' a)
foilPatternNames = \case
  TH.FoilPatternWildcard _  -> []
  TH.FoilPatternVar _ x     -> [nameId (nameOf x)]
  TH.FoilPatternPair _ l r  -> foilPatternNames l ++ foilPatternNames r

-- | The shape of a pattern: where the wildcards, variables and pairs are.
data Shape = Wildcard | Variable | Pair Shape Shape

-- | A shape of nesting depth at most @d@.
genShape :: Int -> Gen Shape
genShape d = frequency $
  [ (1, pure Wildcard), (3, pure Variable) ] ++
  [ (2, Pair <$> genShape (d - 1) <*> genShape (d - 1)) | d > 0 ]

-- | A pattern of the given shape, with hinted names.
instantiate :: Distinct n => Shape -> Scope n -> Gen (PatIn TH.FoilPattern n)
instantiate shape scope = case shape of
  Wildcard -> pure (PatIn (TH.FoilPatternWildcard Nothing))
  Variable -> withHintedBinder scope (pure . PatIn . TH.FoilPatternVar Nothing)
  Pair left right -> do
    PatIn l <- instantiate left scope
    PatIn r <- instantiate right (extendScopePattern l scope)
    pure (PatIn (TH.FoilPatternPair Nothing l r))

-- | Patterns of nesting depth at most two.
genFoilPattern :: GenPattern TH.FoilPattern
genFoilPattern ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  instantiate shape scope

-- | Two patterns of the same shape.
genFoilPatternPair :: GenPatternPair TH.FoilPattern
genFoilPatternPair ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  PatIn l <- instantiate shape scope
  PatIn r <- instantiate shape scope
  pure (PatPair l r)
