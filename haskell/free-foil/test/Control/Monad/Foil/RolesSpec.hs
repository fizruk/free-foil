{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

-- | The scope indices of the foil's types are nominal, so 'coerce' cannot
-- change them, while 'sink' and coercions that keep the scope still work.
--
-- A test that a coercion is rejected needs a program that does not
-- typecheck. This module is compiled with @-fdefer-type-errors@, so each
-- such coercion compiles to a runtime 'TypeError', which the test expects.
-- The same technique is behind the @should-not-typecheck@ package.
-- The module imports only the public modules, where the @Unsafe@
-- constructors are not in scope: with them, 'coerce' would still unwrap the
-- newtypes and succeed.
module Control.Monad.Foil.RolesSpec (spec) where

import           Control.Exception         (TypeError (..), evaluate)
import           Data.Coerce               (coerce)
import           Data.Foldable             (toList)
import           Data.List                 (isInfixOf)
import           Data.Monoid               (Sum (..))
import           Test.Hspec

import           Control.Monad.Foil
import           Control.Monad.Foil.Blocks

-- * Coercions that change a scope index (none of these typecheck)

-- | A name moves to an unrelated scope.
anyName :: Name n -> Name l
anyName = coerce

-- | A name of the inner scope escapes its binder.
escapeName :: NameBinder n l -> Name l -> Name n
escapeName _ = coerce

binderOuter :: NameBinder n l -> NameBinder n' l
binderOuter = coerce

binderInner :: NameBinder n l -> NameBinder n l'
binderInner = coerce

anyScope :: Scope n -> Scope l
anyScope = coerce

anyNameSet :: NameSet n -> NameSet l
anyNameSet = coerce

substDomain :: Substitution e i o -> Substitution e i' o
substDomain = coerce

nameBindersOuter :: NameBinders n l -> NameBinders n' l
nameBindersOuter = coerce

nameBindersInner :: NameBinders n l -> NameBinders n l'
nameBindersInner = coerce

anyNameMap :: NameMap n a -> NameMap l a
anyNameMap = coerce

extWithinOuter :: ExtWithin n l -> ExtWithin n' l
extWithinOuter = coerce

extWithinInner :: ExtWithin n l -> ExtWithin n l'
extWithinInner = coerce

blockOuter :: Block c l -> Block c' l
blockOuter = coerce

blockInner :: Block c l -> Block c l'
blockInner = coerce

scopeUnionLeft :: ScopeUnion n m k -> ScopeUnion n' m k
scopeUnionLeft = coerce

scopeUnionRight :: ScopeUnion n m k -> ScopeUnion n m' k
scopeUnionRight = coerce

scopeUnionWhole :: ScopeUnion n m k -> ScopeUnion n m k'
scopeUnionWhole = coerce

-- | Evaluating the value raises the deferred type error of a 'coerce'.
rejected :: a -> Expectation
rejected x = evaluate x `shouldThrow` coercionRejected

coercionRejected :: Selector TypeError
coercionRejected (TypeError msg) =
  "Couldn't match type" `isInfixOf` msg && "coerce" `isInfixOf` msg

-- * Coercions that keep the scope (these typecheck)

-- | A user newtype over names, as a generated single-binder pattern is.
newtype Var n = Var (Name n)

toVar :: Name n -> Var n
toVar = coerce

valuesAsSum :: NameMap n Int -> NameMap n (Sum Int)
valuesAsSum = coerce

-- | 'sink', with the target scope pinned by a binder the caller holds.
sunkVia :: (Sinkable e, DExt n l) => NameBinder n l -> e n -> e l
sunkVia _ = sink

sunk1Via :: (Functor f, Sinkable e, DExt n l) => NameBinder n l -> f (e n) -> f (e l)
sunk1Via _ = sink1

spec :: Spec
spec = do
  describe "coerce cannot change a scope index" $ do
    it "of a Name" $
      withFresh emptyScope $ \x -> rejected (nameId (anyName (nameOf x)))
    it "of a Name bound by a NameBinder (escaping the binder)" $
      withFresh emptyScope $ \x -> rejected (nameId (escapeName x (nameOf x)))
    it "of a NameBinder (the outer scope)" $
      withFresh emptyScope $ \x -> rejected (nameId (nameOf (binderOuter x)))
    it "of a NameBinder (the inner scope)" $
      withFresh emptyScope $ \x -> rejected (nameId (nameOf (binderInner x)))
    it "of a Scope" $
      rejected (anyScope emptyScope)
    it "of a NameSet" $
      withFresh emptyScope $ \x -> rejected (anyNameSet (nameSetSingleton (nameOf x)))
    it "of a Substitution (the domain)" $
      rejected (substDomain (voidSubst :: Substitution Name VoidS VoidS))
    it "of NameBinders (the outer scope)" $
      rejected (nameBindersOuter (emptyNameBinders :: NameBinders VoidS VoidS))
    it "of NameBinders (the inner scope)" $
      rejected (nameBindersInner (emptyNameBinders :: NameBinders VoidS VoidS))
    it "of a NameMap" $
      rejected (anyNameMap (emptyNameMap :: NameMap VoidS Char))
    it "of ExtWithin (the outer scope)" $
      rejected (extWithinOuter (extWithinRefl (NameRange 0 9) :: ExtWithin VoidS VoidS))
    it "of ExtWithin (the inner scope)" $
      rejected (extWithinInner (extWithinRefl (NameRange 0 9) :: ExtWithin VoidS VoidS))
    it "of a Block (the outer scope)" $
      rejected (blockOuter (beginBlock (NameRange 0 9) :: Block VoidS VoidS))
    it "of a Block (the inner scope)" $
      rejected (blockInner (beginBlock (NameRange 0 9) :: Block VoidS VoidS))
    it "of a ScopeUnion (each of the three scopes)" $
      case checkScopeUnion emptyScope emptyScope emptyScope of
        Nothing -> expectationFailure "the empty scope is the union of two empty scopes"
        Just u -> do
          rejected (scopeUnionLeft u)
          rejected (scopeUnionRight u)
          rejected (scopeUnionWhole u)

  describe "scope changes that remain possible" $ do
    it "sink moves a name to an extended scope" $
      withFresh emptyScope $ \x ->
        withFresh (extendScope x emptyScope) $ \y ->
          nameId (sunkVia y (nameOf x)) `shouldBe` nameId (nameOf x)
    it "sink1 moves a list of names to an extended scope" $
      withFresh emptyScope $ \x ->
        withFresh (extendScope x emptyScope) $ \y ->
          map nameId (sunk1Via y [nameOf x]) `shouldBe` [nameId (nameOf x)]
    it "coerce wraps a name in a user newtype, keeping its scope" $
      withFresh emptyScope $ \x ->
        case toVar (nameOf x) of
          Var x' -> nameId x' `shouldBe` nameId (nameOf x)
    it "coerce changes the values of a NameMap, keeping its scope" $
      withFresh emptyScope $ \x ->
        map getSum (toList (valuesAsSum (addNameBinder x 1 emptyNameMap))) `shouldBe` [1]
