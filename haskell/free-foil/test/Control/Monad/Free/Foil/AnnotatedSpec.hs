{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Annotated syntax: one 'AnnSig' serving two annotations with opposite matching
-- behaviour, and the 'Bifoldable' asymmetry that α-equivalence relies on.
module Control.Monad.Free.Foil.AnnotatedSpec (spec) where

import           Data.Bifunctor.TH
import           Data.Functor.Const                (Const (..))
import           Data.Kind                         (Type)
import           Data.ZipMatchK
import           Generics.Kind.TH                  (deriveGenericK)
import qualified GHC.Generics                      as GHC
import           Test.Hspec

import qualified Control.Monad.Foil                as Foil
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.Annotated

-- | A minimal λ-calculus signature.
data LamSig scope term = AppSig term term | LamSig scope
  deriving (GHC.Generic, Functor, Foldable, Traversable)

deriveBifunctor ''LamSig
deriveBifoldable ''LamSig
deriveBitraversable ''LamSig
deriveGenericK ''LamSig
instance ZipMatchK LamSig

instance ZipMatchK Int where zipMatchWithK = zipMatchViaEq

-- | An annotation that ignores the term — a source position, say — and __is
-- compared__ when matching.
instance Eq a => ZipMatchK (Const (a :: Type)) where
  zipMatchWithK _ (Const l) (Const r)
    | l == r    = Just (Const l)
    | otherwise = Nothing

type Positioned = AnnAST Foil.NameBinder (Const Int) LamSig

-- | An annotation that holds a term at the node's own scope — a type, say.
--
-- It is optional, and it has to be: an annotation holding a term needs a term to
-- hold, so a closed annotated term could not be built at all without either a
-- 'Maybe' or a knot.
newtype TypeOf term = TypeOf (Maybe term)
  deriving (GHC.Generic, Functor, Foldable, Traversable)

deriveGenericK ''TypeOf

-- | Matching __ignores__ the annotation: it always succeeds, pairing the terms it
-- can and dropping what it cannot.
--
-- The /generic/ instance would not do: it compares the annotation's shape, so a
-- node with a memoised type would fail to match the same node without one.
instance ZipMatchK TypeOf where
  zipMatchWithK (f :^: M0) (TypeOf l) (TypeOf r) =
    Just (TypeOf (do { a <- l; b <- r; f a b }))

type Typed = AnnAST Foil.NameBinder TypeOf LamSig

-- | @\\x. x x@, annotated at every node with a source position.
positioned :: Int -> Positioned Foil.VoidS
positioned k = Foil.withFresh Foil.emptyScope $ \binder ->
  case Foil.assertDistinct binder of
    Foil.Distinct ->
      let x = Var (Foil.nameOf binder)
       in AnnNode (Const k)
            (LamSig (ScopedAST binder (AnnNode (Const k) (AppSig x x))))

-- | @\\x. x@, carrying the given type annotation at its root.
typed :: Maybe (Typed Foil.VoidS) -> Typed Foil.VoidS
typed ty = Foil.withFresh Foil.emptyScope $ \binder ->
  case Foil.assertDistinct binder of
    Foil.Distinct ->
      AnnNode (TypeOf ty) (LamSig (ScopedAST binder (Var (Foil.nameOf binder))))

-- | @\\x. x x@, with no type annotations, to have a structurally different term.
selfApp :: Typed Foil.VoidS
selfApp = Foil.withFresh Foil.emptyScope $ \binder ->
  case Foil.assertDistinct binder of
    Foil.Distinct ->
      let x = Var (Foil.nameOf binder)
       in AnnNode (TypeOf Nothing)
            (LamSig (ScopedAST binder (AnnNode (TypeOf Nothing) (AppSig x x))))

spec :: Spec
spec = do
  describe "an annotation that ignores the term (Const)" $ do
    it "matches when the annotations agree" $
      alphaEquiv Foil.emptyScope (positioned 1) (positioned 1) `shouldBe` True

    it "does not match when they differ" $
      alphaEquiv Foil.emptyScope (positioned 1) (positioned 2) `shouldBe` False

  describe "an annotation that holds a term (a type)" $ do
    it "is ignored when matching: terms differing only in their types are alpha-equivalent" $
      -- The property a dependent typechecker needs. It works because Bifoldable
      -- skips the annotation, so alphaEquiv never walks into it.
      alphaEquiv Foil.emptyScope (typed Nothing) (typed (Just (typed Nothing)))
        `shouldBe` True

    it "still distinguishes terms that differ in the term itself" $
      alphaEquiv Foil.emptyScope (typed Nothing) selfApp `shouldBe` False

    it "never forces the annotation: matching is lazy in it" $
      -- The blind instance returns 'Just' unconditionally with a thunked
      -- annotation, so an annotation that is bottom must not break the match.
      -- A strict instance would throw here instead of returning True.
      alphaEquiv Foil.emptyScope
        (typed (Just (error "annotation forced")))
        (typed (Just (error "annotation forced")))
        `shouldBe` True

  describe "freeVarsOfAnnotated" $
    it "sees a variable that freeVarsOf misses, because it occurs in an annotation" $
      Foil.withFresh Foil.emptyScope $ \outer ->
        case Foil.assertDistinct outer of
          Foil.Distinct ->
            let x = Var (Foil.nameOf outer)                      -- free at this scope
                scope = Foil.extendScope outer Foil.emptyScope
             in Foil.withFresh scope $ \inner ->
                  case Foil.assertDistinct inner of
                    Foil.Distinct ->
                      -- \y. y, annotated with a type that mentions x
                      let node = AnnNode (TypeOf (Just x))
                                   (LamSig (ScopedAST inner (Var (Foil.nameOf inner))))
                       in do
                            freeVarsOf node `shouldBe` []
                            length (freeVarsOfAnnotated node) `shouldBe` 1
