{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TemplateHaskell  #-}

-- | The pattern types that 'Control.Monad.Free.Foil.TH.MkFreeFoil.mkFreeFoil'
-- generates: a @newtype@ for a pattern of one constructor with one binding
-- field, and @data@ otherwise. The instances
-- that are not generated take their "Generics.Kind" defaults, which must work
-- for both.
module Control.Monad.Free.Foil.TH.PatternTypesSpec (spec) where

import           Control.Exception                                        (evaluate)
import qualified Control.Monad.Foil                                       as Foil
import           Control.Monad.Foil.Laws
import qualified Control.Monad.Free.Foil                                  as FreeFoil
import           Data.Coerce                                              (coerce)
import qualified Data.Map                                                 as Map
import           Test.Hspec
import           Test.QuickCheck                                          (Gen, arbitrary, frequency)

import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config
import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Declaration
import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsConfig
import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.PatternsSyntax
import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Syntax

spec :: Spec
spec = do
  describe "a pattern of one constructor with one binder (FFPattern)" $ do
    it "is a newtype" $
      $(declarationOf ''FFPattern) `shouldBe` ("newtype", [("FFPatternVar", [""])])
    it "is coercible to its binder" $
      Foil.withFresh Foil.emptyScope $ \binder ->
        case coerce binder of
          FFPatternVar binder' -> Foil.nameOf binder' `shouldBe` Foil.nameOf binder
    it "is as strict as its binder" $
      evaluate (FFPatternVar undefined) `shouldThrow` anyErrorCall
    describe "CoSinkable (generated)" $
      coSinkableSpec namesOfP genP extensionByCoercion
    describe "UnifiablePattern (GenericK default)" $
      unifyPatternsSpec namesOfP genPPair Holds
    it "gives its binder to getNameBinders (HasNameBinders, GenericK default)" $
      Foil.withFresh Foil.emptyScope $ \binder ->
        namesOfNameBinderList (Foil.nameBindersList (Foil.getNameBinders (FFPatternVar binder)))
          `shouldBe` [Foil.nameId (Foil.nameOf binder)]
    describe "α-equivalence (needs SinkableK and UnifiablePattern)" $ do
      it "identifies λx. x and λy. y" $
        alphaEquivTerms (fun x (Var x)) (fun y (Var y)) `shouldBe` True
      it "tells λx. λy. x from λx. λy. y" $
        alphaEquivTerms (fun x (fun y (Var x))) (fun x (fun y (Var y))) `shouldBe` False

  describe "a pattern of one constructor with one nested pattern (FFNPattern)" $ do
    it "is a newtype" $
      $(declarationOf ''FFNPattern) `shouldBe` ("newtype", [("FFNPatternWrap", [""])])
    describe "CoSinkable (generated)" $
      coSinkableSpec (namesOfM . unwrapN) genN extensionByCoercion
    describe "UnifiablePattern (GenericK default)" $
      unifyPatternsSpec (namesOfM . unwrapN) genNPair Holds

  describe "a pattern of several constructors (FFMPattern)" $ do
    it "is data" $
      $(declarationOf ''FFMPattern) `shouldBe`
        ("data",
          [ ("FFMPatternWild", [])
          , ("FFMPatternVar", [""])
          , ("FFMPatternPair", ["", ""]) ])
    describe "CoSinkable (generated)" $
      coSinkableSpec namesOfM genM extensionByCoercion
    describe "UnifiablePattern (GenericK default)" $
      unifyPatternsSpec namesOfM genMPair Holds
    describe "α-equivalence (needs SinkableK and UnifiablePattern)" $ do
      let pair a b = MPatternPair (MPatternVar a) (MPatternVar b)
          funM p body = MFun p (MScopedTerm body)
      it "identifies λ(x, y). x and λ(y, x). y" $
        alphaEquivMTerms (funM (pair mx my) (MVar mx)) (funM (pair my mx) (MVar my)) `shouldBe` True
      it "tells λ(x, y). x from λ(x, y). y" $
        alphaEquivMTerms (funM (pair mx my) (MVar mx)) (funM (pair mx my) (MVar my)) `shouldBe` False
      it "tells λ(x, _). x from λ(_, x). x" $
        alphaEquivMTerms
          (funM (MPatternPair (MPatternVar mx) MPatternWild) (MVar mx))
          (funM (MPatternPair MPatternWild (MPatternVar mx)) (MVar mx))
          `shouldBe` False

  describe "a pattern of one constructor with a binder and an annotation (FFAPattern)" $ do
    it "is data" $
      $(declarationOf ''FFAPattern) `shouldBe` ("data", [("FFAPatternVar", ["", ""])])
    describe "CoSinkable (generated)" $
      coSinkableSpec namesOfA genA extensionByCoercion
    describe "UnifiablePattern (GenericK default)" $
      unifyPatternsSpec namesOfA genAPair Holds
    it "round-trips through the conversions" $ do
      let term = AFun (APatternVar 7 ax) (AScopedTerm (AVar ax))
      case roundtripA term of
        AFun (APatternVar 7 binder) (AScopedTerm (AVar v)) -> v `shouldBe` binder
        other -> expectationFailure ("unexpected shape: " <> show other)
  where
    x = VarIdent "x"
    y = VarIdent "y"
    fun v body = Fun (PatternVar v) (ScopedTerm body)
    mx = MVarIdent "x"
    my = MVarIdent "y"
    ax = AVarIdent "x"

-- * Single binders

namesOfP :: PatternNames FFPattern
namesOfP (FFPatternVar binder) = [Foil.nameId (Foil.nameOf binder)]

genP :: GenPattern FFPattern
genP ctx = do
  PatIn binder <- genNameBinder ctx
  pure (PatIn (FFPatternVar binder))

genPPair :: GenPatternPair FFPattern
genPPair ctx = do
  PatIn l <- genP ctx
  PatIn r <- genP ctx
  pure (PatPair l r)

alphaEquivTerms :: Term -> Term -> Bool
alphaEquivTerms l r =
  FreeFoil.alphaEquiv Foil.emptyScope
    (toTerm Foil.emptyScope Map.empty l)
    (toTerm Foil.emptyScope Map.empty r)

namesOfNameBinderList :: Foil.NameBinderList n l -> [Int]
namesOfNameBinderList = \case
  Foil.NameBinderListEmpty       -> []
  Foil.NameBinderListCons b rest -> Foil.nameId (Foil.nameOf b) : namesOfNameBinderList rest

-- * Several constructors

namesOfM :: PatternNames FFMPattern
namesOfM = \case
  FFMPatternWild     -> []
  FFMPatternVar b    -> [Foil.nameId (Foil.nameOf b)]
  FFMPatternPair l r -> namesOfM l ++ namesOfM r

-- | The shape of a pattern: where the wildcards, variables and pairs are. This
-- follows the generators of @lambda-pi@'s @LawsSyntax@.
data Shape = Wildcard | Variable | Pair Shape Shape

-- | A shape of nesting depth at most @d@.
genShape :: Int -> Gen Shape
genShape d = frequency $
  [ (1, pure Wildcard), (3, pure Variable) ] ++
  [ (2, Pair <$> genShape (d - 1) <*> genShape (d - 1)) | d > 0 ]

-- | A pattern of the given shape, with hinted names.
instantiate :: Foil.Distinct n => Shape -> Foil.Scope n -> Gen (PatIn FFMPattern n)
instantiate shape scope = case shape of
  Wildcard -> pure (PatIn FFMPatternWild)
  Variable -> withHintedBinder scope (pure . PatIn . FFMPatternVar)
  Pair left right -> do
    PatIn l <- instantiate left scope
    PatIn r <- instantiate right (Foil.extendScopePattern l scope)
    pure (PatIn (FFMPatternPair l r))

genM :: GenPattern FFMPattern
genM ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  instantiate shape scope

genMPair :: GenPatternPair FFMPattern
genMPair ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  PatIn l <- instantiate shape scope
  PatIn r <- instantiate shape scope
  pure (PatPair l r)

alphaEquivMTerms :: MTerm -> MTerm -> Bool
alphaEquivMTerms l r =
  FreeFoil.alphaEquiv Foil.emptyScope
    (toMTerm Foil.emptyScope Map.empty l)
    (toMTerm Foil.emptyScope Map.empty r)

-- * A nested pattern

unwrapN :: FFNPattern n l -> FFMPattern n l
unwrapN (FFNPatternWrap p) = p

genN :: GenPattern FFNPattern
genN ctx = do
  PatIn p <- genM ctx
  pure (PatIn (FFNPatternWrap p))

genNPair :: GenPatternPair FFNPattern
genNPair ctx = do
  PatPair l r <- genMPair ctx
  pure (PatPair (FFNPatternWrap l) (FFNPatternWrap r))

-- * A binder with an annotation

namesOfA :: PatternNames FFAPattern
namesOfA (FFAPatternVar _ binder) = [Foil.nameId (Foil.nameOf binder)]

genA :: GenPattern FFAPattern
genA ctx = do
  annotation <- arbitrary
  PatIn binder <- genNameBinder ctx
  pure (PatIn (FFAPatternVar annotation binder))

genAPair :: GenPatternPair FFAPattern
genAPair ctx = do
  PatIn l <- genA ctx
  PatIn r <- genA ctx
  pure (PatPair l r)

roundtripA :: ATerm -> ATerm
roundtripA = fromATerm . toATerm Foil.emptyScope Map.empty
