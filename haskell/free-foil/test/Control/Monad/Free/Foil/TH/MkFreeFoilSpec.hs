{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Regression tests for 'mkFreeFoil' and 'mkFreeFoilConversions' on raw
-- constructors whose shape does not line up with the free foil node they become.
--
-- That "Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Syntax" compiles at all is half
-- the test: the generated pattern synonyms and conversions used to be ill-typed
-- for @Let@ and @LetRec@. These examples are the other half — they check that a
-- raw binder still binds what it used to.
module Control.Monad.Free.Foil.TH.MkFreeFoilSpec (spec) where

import qualified Control.Monad.Foil                               as Foil
import qualified Data.Map                                         as Map
import           Test.Hspec

import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Config
import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Syntax

-- | Convert a closed raw term into the scope-safe representation and back.
--
-- Binders come back renamed (that is what 'intToVarIdent' is for), so the
-- examples below check how names /relate/, not what they are called.
roundtrip :: Term -> Term
roundtrip = fromTerm . toTerm Foil.emptyScope Map.empty

x, y :: VarIdent
x = VarIdent "x"
y = VarIdent "y"

-- | A closed term, to use where a term must not mention the surrounding binder.
identity :: Term
identity = Fun (PatternVar y) (ScopedTerm (Var y))

spec :: Spec
spec = do
  describe "a pattern adjacent to its scope (Fun)" $
    it "round-trips, and the body still refers to the binder" $
      case roundtrip (Fun (PatternVar x) (ScopedTerm (Var x))) of
        Fun (PatternVar binder) (ScopedTerm (Var v)) -> v `shouldBe` binder
        other -> expectationFailure ("unexpected shape: " <> show other)

  describe "a pattern separated from its scope (Let)" $ do
    it "puts the binder in the binding position, not the bound term's" $
      -- The generated conversions used to hand the raw constructor its arguments
      -- in the free foil node's order rather than the raw one, which put the
      -- bound term where the pattern belongs.
      case roundtrip (Let (PatternVar x) identity (ScopedTerm (Var x))) of
        Let (PatternVar binder) bound (ScopedTerm (Var v)) -> do
          v `shouldBe` binder                 -- the body refers to the binder
          bound `shouldSatisfy` isFun         -- the bound term is still a term
        other -> expectationFailure ("unexpected shape: " <> show other)

  describe "one pattern binding two scopes (LetRec)" $ do
    it "binds the same name in both scopes" $
      -- Each scoped child of a free foil node carries its own binder, so the two
      -- scopes get two distinct foil names. The raw syntax has only one pattern,
      -- so converting back must give both scopes the same name again.
      case roundtrip (LetRec (PatternVar x) (ScopedTerm (Var x)) (ScopedTerm (Var x))) of
        LetRec (PatternVar binder) (ScopedTerm (Var v1)) (ScopedTerm (Var v2)) -> do
          v1 `shouldBe` binder
          v2 `shouldBe` binder
        other -> expectationFailure ("unexpected shape: " <> show other)

    it "keeps the two scopes apart" $
      case roundtrip (LetRec (PatternVar x) (ScopedTerm identity) (ScopedTerm (Var x))) of
        LetRec (PatternVar binder) (ScopedTerm first) (ScopedTerm (Var v)) -> do
          first `shouldSatisfy` isFun   -- the first scope does not mention the binder
          v `shouldBe` binder           -- the second one does
        other -> expectationFailure ("unexpected shape: " <> show other)
  where
    isFun Fun{} = True
    isFun _     = False
