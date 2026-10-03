{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
-- | The laws of "Control.Monad.Foil.Laws" and "Control.Monad.Free.Foil.Laws"
-- for the terms of the minimal Martin-Löf type theory
-- ("Language.MLTT.Impl.Generated"), with patterns that are wildcards,
-- variables and pairs, and the 'Control.Monad.Foil.CoSinkable' instance
-- that 'Control.Monad.Free.Foil.TH.mkFreeFoil' generates for them.
module Language.MLTT.LawsSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Laws
import           Control.Monad.Free.Foil.Laws
import           Language.MLTT.Impl.Generated
import qualified Language.MLTT.Syntax.Abs      as Raw

-- | The shape of a pattern: where the wildcards, variables and pairs are.
data Shape = ShapeWildcard | ShapeVariable | ShapePair Shape Shape

-- | A shape of nesting depth at most @d@.
genShape :: Int -> Gen Shape
genShape d = frequency $
  [ (1, pure ShapeWildcard), (3, pure ShapeVariable) ] ++
  [ (2, ShapePair <$> genShape (d - 1) <*> genShape (d - 1)) | d > 0 ]

-- | A pattern of the given shape, with hinted names.
instantiate :: Distinct n => Shape -> Scope n -> Gen (PatIn (Pattern' Raw.BNFC'Position) n)
instantiate shape scope = case shape of
  ShapeWildcard -> pure (PatIn (PatternWildcard Nothing))
  ShapeVariable -> withHintedBinder scope (pure . PatIn . PatternVar Nothing)
  ShapePair left right -> do
    PatIn l <- instantiate left scope
    PatIn r <- instantiate right (extendScopePattern l scope)
    pure (PatIn (PatternPair Nothing l r))

genPattern :: GenPattern (Pattern' Raw.BNFC'Position)
genPattern ctx = withCtx ctx $ \scope -> genShape 2 >>= \shape -> instantiate shape scope

genPatternPair :: GenPatternPair (Pattern' Raw.BNFC'Position)
genPatternPair ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  PatIn l <- instantiate shape scope
  PatIn r <- instantiate shape scope
  pure (PatPair l r)

-- | The names a pattern binds, left to right.
patternNames :: PatternNames (Pattern' a)
patternNames = \case
  PatternWildcard _  -> []
  PatternVar _ x     -> [nameId (nameOf x)]
  PatternPair _ l r  -> patternNames l ++ patternNames r

-- | All constructors of the signature. Locations are 'Nothing'.
termSyntax :: SyntaxGen (Pattern' Raw.BNFC'Position) (Term'Sig Raw.BNFC'Position)
termSyntax = SyntaxGen
  { sgShapes =
      [ PiSig loc () (), SigmaSig loc () (), LamSig loc (), LetSig loc () ()
      , ArrowSig loc () (), ProductSig loc () (), AppSig loc () ()
      , FirstSig loc (), SecondSig loc ()
      , UniverseSig loc, UnitTypeSig loc, UnitValSig loc
      , IdTypeSig loc () () (), ReflSig loc (), JSig loc () () ()
      , PairSig loc () (), AnnSig loc () () ]
  , sgPattern = genPattern
  , sgPatternNames = patternNames
  , sgShowNode = \case
      PiSig _ a b        -> "Π(" <> a <> ") " <> b
      SigmaSig _ a b     -> "Σ(" <> a <> ") " <> b
      LamSig _ b         -> b
      LetSig _ a b       -> "let " <> a <> " in " <> b
      ArrowSig _ a b     -> "(" <> a <> " → " <> b <> ")"
      ProductSig _ a b   -> "(" <> a <> " × " <> b <> ")"
      AppSig _ f x       -> "(" <> f <> " " <> x <> ")"
      FirstSig _ t       -> "π₁(" <> t <> ")"
      SecondSig _ t      -> "π₂(" <> t <> ")"
      UniverseSig _      -> "𝕌"
      UnitTypeSig _      -> "𝟙"
      UnitValSig _       -> "()"
      IdTypeSig _ a x y  -> "Id(" <> a <> ", " <> x <> ", " <> y <> ")"
      ReflSig _ t        -> "refl(" <> t <> ")"
      JSig _ a b c       -> "J(" <> a <> ", " <> b <> ", " <> c <> ")"
      PairSig _ l r      -> "(" <> l <> ", " <> r <> ")"
      AnnSig _ t a       -> "(" <> t <> " : " <> a <> ")"
  }
  where
    loc = Nothing

spec :: Spec
spec = do
  describe "CoSinkable Pattern" $ coSinkableSpec patternNames genPattern extensionByCoercion
  describe "UnifiablePattern Pattern" $
    unifyPatternsSpec patternNames genPatternPair mergedBinderRenamings
  describe "α-equivalence" $ alphaSpec termSyntax $ \case
    AlphaEquivRefreshedAgrees -> Holds
    _                         -> mergedBinderRenamings
  describe "relative monad" $ relMonadSpec termSyntax (\_ _ -> Holds)
  describe "functor" $ functorSpec termSyntax (\_ _ -> genericSinkableCrash) $ \cls -> \case
    SinkAgreesWithLiftRM -> genericSinkAgreesWithLiftRM cls
    _                    -> Holds
