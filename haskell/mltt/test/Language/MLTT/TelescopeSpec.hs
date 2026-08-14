{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | A telescope as a foil pattern.
--
-- The interesting property is the one the foil's pattern API does not give for
-- free. A telescope carries a payload per step, and refreshing the telescope
-- has to rename the payloads along with the binders, since a payload may
-- mention the binders before it. 'Control.Monad.Foil.withPattern' relates the
-- telescope's own scope to the ambient one only through the binders it hands
-- back, so the renaming is recovered from those, and the tests below pin both
-- halves of that: the payload follows a renamed binder, and it is left alone
-- when nothing is renamed.
module Language.MLTT.TelescopeSpec (spec) where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil      (pattern Var, supportOf)
import           Language.MLTT.Impl.Generated
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Telescope
import           Test.Hspec

pos :: Raw.BNFC'Position
pos = Raw.BNFC'NoPosition

-- | @(A : 𝕌) (x : A)@, allocated from the empty scope, so its binders are the
-- raw names 0 and 1 and its second payload mentions the first binder.
withDependent
  :: (forall l. Foil.Distinct l
        => ParamTelescope Raw.BNFC'Position Foil.VoidS l -> r)
  -> r
withDependent cont =
  Foil.withFresh Foil.emptyScope $ \bA ->
    Foil.withFresh (Foil.extendScope bA Foil.emptyScope) $ \bx ->
      cont $
        TelescopeCons (Raw.VarIdent "A") (Universe pos) bA $
          TelescopeCons (Raw.VarIdent "x") (Var (Foil.nameOf bA)) bx TelescopeEmpty

-- | @(A : 𝕌) (x : A)@ again, but allocated from a given range, so that two of
-- these can start in the same scope with different binders. That is the pair
-- whose payloads only agree once the binders have been identified.
withDependentIn
  :: Foil.NameRange
  -> (forall l. Foil.Distinct l
        => ParamTelescope Raw.BNFC'Position Foil.VoidS l -> r)
  -> r
withDependentIn range cont =
  Foil.withFreshIn range Foil.emptyScope $ \bA ->
    Foil.withFreshIn range (Foil.extendScope bA Foil.emptyScope) $ \bx ->
      cont $
        TelescopeCons (Raw.VarIdent "A") (Universe pos) bA $
          TelescopeCons (Raw.VarIdent "x") (Var (Foil.nameOf bA)) bx TelescopeEmpty

-- | @(A : 𝕌) (x : 𝟙)@: the same binders as 'withDependent', and a second
-- payload that does not name the first binder.
withUnrelated
  :: (forall l. Foil.Distinct l
        => ParamTelescope Raw.BNFC'Position Foil.VoidS l -> r)
  -> r
withUnrelated cont =
  Foil.withFresh Foil.emptyScope $ \bA ->
    Foil.withFresh (Foil.extendScope bA Foil.emptyScope) $ \bx ->
      cont $
        TelescopeCons (Raw.VarIdent "A") (Universe pos) bA $
          TelescopeCons (Raw.VarIdent "x") (UnitType pos) bx TelescopeEmpty

-- | @(A : 𝕌)@, for comparing telescopes of different lengths.
withSingle
  :: (forall l. Foil.Distinct l
        => ParamTelescope Raw.BNFC'Position Foil.VoidS l -> r)
  -> r
withSingle cont =
  Foil.withFresh Foil.emptyScope $ \bA ->
    cont (TelescopeCons (Raw.VarIdent "A") (Universe pos) bA TelescopeEmpty)

-- | A scope holding the raw names 0 and 1, so that both binders of
-- 'withDependent' clash with it.
withClashingScope :: (forall o. Foil.Distinct o => Foil.Scope o -> r) -> r
withClashingScope cont =
  Foil.withFresh Foil.emptyScope $ \b0 ->
    let scope1 = Foil.extendScope b0 Foil.emptyScope
     in Foil.withFresh scope1 $ \b1 -> cont (Foil.extendScope b1 scope1)

-- | Refresh a telescope, fixing the expression type that
-- 'Foil.withRefreshedPattern' leaves for the caller to choose.
withRefreshedTelescope
  :: Foil.Distinct o
  => Foil.Scope o
  -> ParamTelescope Raw.BNFC'Position n l
  -> (forall o'. Foil.DExt o o'
        => ParamTelescope Raw.BNFC'Position o o' -> r)
  -> r
withRefreshedTelescope scope tele cont =
  Foil.withRefreshedPattern scope tele $
    \(_ :: Foil.Substitution Term n' o -> Foil.Substitution Term l' o') tele' ->
      cont tele'

-- | The raw names of the binders, outermost first.
binderNames :: Telescope label e n l -> [Foil.RawName]
binderNames = go . telescopeBinders
  where
    go :: Foil.NameBinderList n' l' -> [Foil.RawName]
    go Foil.NameBinderListEmpty            = []
    go (Foil.NameBinderListCons binder bs) =
      Foil.nameId (Foil.nameOf binder) : go bs

-- | The raw names each payload mentions, outermost first.
payloadNames :: Foil.Distinct n => ParamTelescope a n l -> [[Foil.RawName]]
payloadNames TelescopeEmpty = []
payloadNames (TelescopeCons _ ty binder rest) =
  case Foil.assertDistinct binder of
    Foil.Distinct ->
      map Foil.nameId (Foil.nameSetToList (supportOf ty)) : payloadNames rest

-- | Whether unification found the two telescopes to bind the same names.
sameBinders :: Foil.UnifyNameBinders binder n l r -> Bool
sameBinders Foil.SameNameBinders{} = True
sameBinders _                      = False

-- | Whether unification succeeded at all, renaming or not.
unifiable :: Foil.UnifyNameBinders binder n l r -> Bool
unifiable Foil.NotUnifiable = False
unifiable _                 = True

spec :: Spec
spec = do
  describe "the binders of a telescope" $ do
    it "are the same through the pattern API as directly" $
      withDependent $ \tele ->
        map Foil.nameId (Foil.namesOfPattern tele) `shouldBe` binderNames tele

    it "all extend the ambient scope" $
      withDependent $ \tele ->
        let scope = Foil.extendScopePattern tele Foil.emptyScope
         in map Foil.nameId (Foil.nameSetToList (Foil.scopeToNameSet scope))
              `shouldBe` binderNames tele

  describe "refreshing a telescope" $ do
    it "leaves the payloads alone when no binder clashes" $
      withDependent $ \tele ->
        withRefreshedTelescope Foil.emptyScope tele $ \tele' ->
          (binderNames tele', payloadNames tele') `shouldBe` ([0, 1], [[], [0]])

    it "carries a payload's reference to a renamed binder along" $
      -- Both binders are renamed, so the second payload, which is `A`, has to
      -- come out mentioning the new first binder rather than the old one.
      withDependent $ \tele ->
        withClashingScope $ \scope ->
          withRefreshedTelescope scope tele $ \tele' ->
            (binderNames tele', payloadNames tele') `shouldBe` ([2, 3], [[], [2]])

  describe "unifying telescopes" $ do
    it "unifies a telescope with itself" $
      withDependent $ \tele ->
        sameBinders (Foil.unifyPatterns tele tele) `shouldBe` True

    it "ignores the labels, as it ignores a bound variable's spelling" $
      withDependent $ \tele ->
        sameBinders (Foil.unifyPatterns tele (relabel tele)) `shouldBe` True

    it "refuses telescopes of different lengths" $
      withDependent $ \long ->
        withSingle $ \short ->
          sameBinders (Foil.unifyPatterns long short) `shouldBe` False

  describe "unifying telescopes in a scope" $ do
    it "identifies two whose binders were allocated in different ranges" $
      -- The binders are 0, 1 on the left and 10, 11 on the right, so the second
      -- payloads are `A` and `B`, which are different names. They agree only
      -- once the first binders have been identified, which is the renaming the
      -- verdict prescribes and the reason the payloads cannot be compared as
      -- they stand.
      withDependentIn (Foil.NameRange 0 9) $ \tele1 ->
        withDependentIn (Foil.NameRange 10 19) $ \tele2 ->
          unifiable (Foil.unifyPatternsIn Foil.emptyScope tele1 tele2)
            `shouldBe` True

    it "tells apart two whose payloads differ" $
      -- @(A : 𝕌) (x : A)@ against @(A : 𝕌) (x : 𝟙)@: the same binders, and a
      -- second payload that is not the same type.
      withDependent $ \tele1 ->
        withUnrelated $ \tele2 ->
          unifiable (Foil.unifyPatternsIn Foil.emptyScope tele1 tele2)
            `shouldBe` False

    it "is what the binder-only approximation cannot see" $
      -- The contrast with the test above: 'Foil.unifyPatterns' has no scope, so
      -- it compares the binders and reports the two as the same pattern.
      withDependent $ \tele1 ->
        withUnrelated $ \tele2 ->
          sameBinders (Foil.unifyPatterns tele1 tele2) `shouldBe` True
  where
    relabel :: ParamTelescope a n l -> ParamTelescope a n l
    relabel TelescopeEmpty = TelescopeEmpty
    relabel (TelescopeCons _ ty binder rest) =
      TelescopeCons (Raw.VarIdent "renamed") ty binder (relabel rest)
