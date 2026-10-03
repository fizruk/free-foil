{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | The laws for the λΠ-calculus of "Language.LambdaPi.Impl.Foil", the
-- plain foil with hand-written instances. Terms are generated and compared
-- through "Language.LambdaPi.Impl.FreeFoilTH", which has the same
-- constructors and the same patterns.
module Language.LambdaPi.Impl.FoilLawsSpec (spec) where

import           Test.Hspec

import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil             (AST (..), ScopedAST (..))
import           Control.Monad.Free.Foil.Laws.Mirror
import qualified Language.LambdaPi.Impl.Foil         as F
import qualified Language.LambdaPi.Impl.FreeFoilTH   as TH
import           Language.LambdaPi.Impl.LawsSyntax   (genFoilPattern, genFoilPatternPair,
                                                      termSyntax)
import           Control.Monad.Foil                  (nameId, nameOf)
import qualified Language.LambdaPi.Syntax.Abs        as Raw

-- | The generated term with the same structure, without locations.
toTerm :: F.Expr n -> TH.Term n
toTerm = \case
  F.VarE x        -> Var x
  F.AppE f x      -> Node (TH.AppSig loc (toTerm f) (toTerm x))
  F.LamE p body   -> Node (TH.LamSig loc (ScopedAST (toPattern p) (toTerm body)))
  F.PiE p a body  -> Node (TH.PiSig loc (toTerm a) (ScopedAST (toPattern p) (toTerm body)))
  F.PairE l r     -> Node (TH.PairSig loc (toTerm l) (toTerm r))
  F.FirstE t      -> Node (TH.FirstSig loc (toTerm t))
  F.SecondE t     -> Node (TH.SecondSig loc (toTerm t))
  F.ProductE l r  -> Node (TH.ProductSig loc (toTerm l) (toTerm r))
  F.UniverseE     -> Node (TH.UniverseSig loc)
  where
    loc = Nothing

-- | The hand-written term with the same structure.
fromTerm :: TH.Term n -> F.Expr n
fromTerm = \case
  Var x -> F.VarE x
  Node node -> case node of
    TH.AppSig _ f x                     -> F.AppE (fromTerm f) (fromTerm x)
    TH.LamSig _ (ScopedAST p body)      -> F.LamE (fromPattern p) (fromTerm body)
    TH.PiSig _ a (ScopedAST p body)     -> F.PiE (fromPattern p) (fromTerm a) (fromTerm body)
    TH.PairSig _ l r                    -> F.PairE (fromTerm l) (fromTerm r)
    TH.FirstSig _ t                     -> F.FirstE (fromTerm t)
    TH.SecondSig _ t                    -> F.SecondE (fromTerm t)
    TH.ProductSig _ l r                 -> F.ProductE (fromTerm l) (fromTerm r)
    TH.UniverseSig _                    -> F.UniverseE

toPattern :: F.Pattern n l -> TH.FoilPattern n l
toPattern = \case
  F.PatternWildcard -> TH.FoilPatternWildcard Nothing
  F.PatternVar x    -> TH.FoilPatternVar Nothing x
  F.PatternPair l r -> TH.FoilPatternPair Nothing (toPattern l) (toPattern r)

fromPattern :: TH.FoilPattern' a n l -> F.Pattern n l
fromPattern = \case
  TH.FoilPatternWildcard _  -> F.PatternWildcard
  TH.FoilPatternVar _ x     -> F.PatternVar x
  TH.FoilPatternPair _ l r  -> F.PatternPair (fromPattern l) (fromPattern r)

-- | The names a pattern binds, left to right.
patternNames :: PatternNames F.Pattern
patternNames = \case
  F.PatternWildcard -> []
  F.PatternVar x    -> [nameId (nameOf x)]
  F.PatternPair l r -> patternNames l ++ patternNames r

-- | Patterns, through the generated ones.
genPattern :: GenPattern F.Pattern
genPattern ctx = do
  PatIn p <- genFoilPattern ctx
  pure (PatIn (fromPattern p))

-- | Pairs of patterns of the same shape.
genPatternPair :: GenPatternPair F.Pattern
genPatternPair ctx = do
  PatPair l r <- genFoilPatternPair ctx
  pure (PatPair (fromPattern l) (fromPattern r))

mirror :: Mirror TH.FoilPattern (TH.Term'Sig Raw.BNFC'Position) F.Expr
mirror = Mirror
  { mirrorSyntax = termSyntax
  , mirrorFrom = fromTerm
  , mirrorTo = toTerm
  , mirrorSubstitute = F.substitute
  , mirrorAlphaEquiv = Just (AlphaEquivOf F.alphaEquiv)
  }

spec :: Spec
spec = do
  describe "CoSinkable Pattern" $ coSinkableSpec patternNames genPattern extensionByCoercion
  describe "UnifiablePattern Pattern" $
    unifyPatternsSpec patternNames genPatternPair mergedBinderRenamings
  mirrorSpec mirror $ \cls -> \case
    MirrorSinkAgreesWithLiftRM | cls /= Inclusions -> KnownFailure
      "extendRenaming is a coercion, so free names under a binder are not renamed"
    MirrorAlphaEquivRefresh -> mergedBinderRenamings
    -- 'F.alphaEquiv' pushes the verdict's renaming through a body with
    -- 'liftRM'. When a binder of the left pattern shadows a name of the scope
    -- (a term built in a small scope and sunk), the right binder renamed to it
    -- is conflated with a free occurrence of that name on the right, as in
    -- λx0. x0 against λx1. x0 in the scope {x0}. On patterns of several
    -- binders, the law also fails as 'mergedBinderRenamings' says, but the
    -- capture remains once that is fixed.
    MirrorAlphaEquivAgrees  -> KnownFailure
      "renaming a right binder to a left binder that shadows the scope captures a free name"
    _ -> Holds
