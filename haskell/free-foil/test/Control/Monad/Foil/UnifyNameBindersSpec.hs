{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | 'Foil.unifyNameBinders' renames the binder with the /larger/ name towards the
-- one with the smaller name. This module pins that down, because the choice looks
-- arbitrary and is not: it is safe, but only because the renaming it asks for is
-- applied by a capture-avoiding substitution.
--
-- A fresh name is @max scope + 1@, so binder names normally grow as one goes
-- deeper into a term. They do not have to: 'Foil.sink' is a coercion, so a term
-- built in a small scope keeps its (small) binder names when it is placed inside
-- a larger one. A term whose /outer/ binder is named after its /inner/ one is
-- therefore reachable, and it is the term that makes the direction of the
-- renaming observable.
module Control.Monad.Foil.UnifyNameBindersSpec (spec) where

import           Data.Maybe                                       (fromJust)
import           Test.Hspec

import qualified Control.Monad.Foil                               as Foil
import           Control.Monad.Free.Foil

import           Control.Monad.Free.Foil.TH.MkFreeFoilSpec.Syntax

-- | @\\x. x@, with the binder named @max scope + 1@.
identityIn :: Foil.Distinct n => Foil.Scope n -> FFTerm n
identityIn scope = Foil.withFresh scope $ \binder ->
  case Foil.assertDistinct binder of
    Foil.Distinct -> FFFun (FFPatternVar binder) (Var (Foil.nameOf binder))

-- | @\\x. \\y. y@, built outside-in: the outer binder is named 0, the inner 1.
nestedNormal :: FFTerm Foil.VoidS
nestedNormal = Foil.withFresh Foil.emptyScope $ \outer ->
  case Foil.assertDistinct outer of
    Foil.Distinct ->
      FFFun (FFPatternVar outer) (identityIn (Foil.extendScope outer Foil.emptyScope))

-- | The same term, @\\x. \\y. y@, built inside-out: the outer binder is named 1
-- and the inner one 0, so the names run backwards.
nestedInverted :: FFTerm Foil.VoidS
nestedInverted = fromJust $
  Foil.withFresh Foil.emptyScope $ \(binder0 :: Foil.NameBinder Foil.VoidS n1) ->
    case Foil.assertDistinct binder0 of
      Foil.Distinct ->
        let scope1 = Foil.extendScope binder0 Foil.emptyScope
            inner  = Foil.sink (identityIn Foil.emptyScope) :: FFTerm n1  -- binder named 0
         in Foil.withFresh scope1 $ \outer ->                             -- named 1
              case Foil.assertDistinct outer of
                Foil.Distinct ->
                  unsinkAST Foil.emptyScope
                    (FFFun (FFPatternVar outer) (Foil.sink inner))

spec :: Spec
spec = describe "unifyNameBinders (via alphaEquiv)" $ do
  it "identifies two spellings of the same term whose binder names run opposite ways" $
    -- Unifying the two outer binders renames the right one (1) down to the left
    -- one (0) -- onto a name a binder /inside that very body/ already uses. The
    -- renaming is applied with 'liftRM', which refreshes on a clash, so it does
    -- not capture. Renaming towards the smaller name is therefore safe, and this
    -- is the example that says so.
    alphaEquiv Foil.emptyScope nestedNormal nestedInverted `shouldBe` True

  it "is symmetric on that pair" $
    alphaEquiv Foil.emptyScope nestedInverted nestedNormal `shouldBe` True

  it "still tells genuinely different terms apart" $
    alphaEquiv Foil.emptyScope nestedNormal (identityIn Foil.emptyScope) `shouldBe` False
