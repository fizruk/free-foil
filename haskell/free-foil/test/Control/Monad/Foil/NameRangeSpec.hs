{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Properties of range-guarded allocation ('Foil.rawFreshNameIn',
-- 'Foil.withFreshIn'), including scopes with negative and extreme names.
--
-- Allocation is a soundness surface: 'Foil.sink' rests on every allocated
-- name being fresh in the ambient scope. The properties here pin the
-- freshness claim, the exhaustion behaviour, and the overflow guards, and
-- check that 'Data.IntSet' handles the sign bit the way the allocator
-- assumes (against a 'Data.Set' model).
module Control.Monad.Foil.NameRangeSpec (spec) where

import           Data.IntSet                 (IntSet)
import qualified Data.IntSet                 as IntSet
import           Data.List                   (sort)
import           Data.Maybe                  (isNothing)
import qualified Data.Set                    as Set
import           Test.Hspec
import           Test.Hspec.QuickCheck       (prop)
import           Test.QuickCheck

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Foil.Internal (NameRange (..), rawFreshName,
                                              rawFreshNameIn)

-- | Raw names biased towards small values, negatives, and the extremes,
-- so that the sign bit and the overflow guards are actually exercised.
genRawName :: Gen Int
genRawName = frequency
  [ (4, choose (-20, 20))
  , (2, arbitrary)
  , (1, elements [minBound, minBound + 1, -1, 0, 1, maxBound - 1, maxBound])
  ]

genRawScope :: Gen IntSet
genRawScope = IntSet.fromList <$> listOf genRawName

-- | A (possibly empty) range with the same bias as 'genRawName'.
genNameRange :: Gen NameRange
genNameRange = do
  a <- genRawName
  b <- genRawName
  frequency
    [ (4, pure (NameRange (min a b) (max a b)))
    , (1, pure (NameRange a b))  -- possibly empty (lo > hi)
    ]

spec :: Spec
spec = do
  describe "rawFreshNameIn" $ do
    prop "allocates inside the range and fresh in the whole scope" $
      forAll genNameRange $ \range@(NameRange lo hi) ->
        forAll genRawScope $ \scope ->
          case rawFreshNameIn range scope of
            Nothing -> discard
            Just x  -> conjoin
              [ counterexample "below range" (x >= lo)
              , counterexample "above range" (x <= hi)
              , counterexample "not fresh" (not (IntSet.member x scope))
              ]

    prop "is exhausted exactly when the range is empty or its top is taken" $
      forAll genNameRange $ \range@(NameRange lo hi) ->
        forAll genRawScope $ \scope ->
          isNothing (rawFreshNameIn range scope)
            === (lo > hi || IntSet.member hi scope)

    prop "agrees with rawFreshName on non-negative scopes" $
      forAll (IntSet.fromList . map getNonNegative <$> arbitrary) $ \scope ->
        rawFreshNameIn Foil.fullNameRange scope === Just (rawFreshName scope)

    it "does not reuse a taken name at hi = maxBound (lookupLT overflow)" $
      -- The formulation via @IntSet.lookupLT (hi + 1)@ would wrap around
      -- and return 'Just 0' here.
      rawFreshNameIn (NameRange 0 maxBound) (IntSet.fromList [0])
        `shouldBe` Just 1

    it "does not wrap past a taken maxBound (successor overflow)" $
      -- The successor of @maxBound@ wraps to @minBound@; the range must
      -- report exhaustion instead.
      rawFreshNameIn (NameRange maxBound maxBound) (IntSet.fromList [maxBound])
        `shouldBe` Nothing

    it "allocates minBound from an empty scope" $
      rawFreshNameIn (NameRange minBound minBound) IntSet.empty
        `shouldBe` Just minBound

    it "reports an empty range as exhausted" $
      rawFreshNameIn (NameRange 5 4) IntSet.empty `shouldBe` Nothing

  describe "withFreshIn" $ do
    it "allocates the low end of an untouched range" $
      Foil.withFreshIn (NameRange 100 199) Foil.emptyScope $ \binder ->
        Foil.nameId (Foil.nameOf binder) `shouldBe` 100

    it "skips scope members inside the range, ignores those outside" $
      Foil.withFresh Foil.emptyScope $ \b0 ->                      -- name 0
        let scope0 = Foil.extendScope b0 Foil.emptyScope
         in Foil.withFreshIn (NameRange (-10) (-1)) scope0 $ \bneg ->  -- name -10
              let scope1 = Foil.extendScope bneg scope0
               in Foil.withFreshIn (NameRange (-10) (-1)) scope1 $ \bneg' -> do
                    Foil.nameId (Foil.nameOf bneg) `shouldBe` (-10)
                    Foil.nameId (Foil.nameOf bneg') `shouldBe` (-9)

    it "reports exhaustion through tryWithFreshIn" $
      Foil.withFresh Foil.emptyScope $ \b0 ->
        let scope0 = Foil.extendScope b0 Foil.emptyScope
         in Foil.tryWithFreshIn (NameRange 0 0) scope0 (\_ -> ())
              `shouldBe` Nothing

  describe "withFreshNameBinderListIn" $
    it "allocates consecutive names from the range's low end" $
      Foil.withFreshNameBinderListIn (NameRange 50 59) "abc"
        Foil.emptyScope Foil.emptyNameMap $ \_scope binders _nameMap ->
          binderIds binders `shouldBe` [50, 51, 52]

  describe "NameMap over negative names" $
    it "addNameBinder/lookupName/popNameBinder round-trip" $
      Foil.withFreshIn (NameRange (-100) (-1)) Foil.emptyScope $ \binder -> do
        let nameMap = Foil.addNameBinder binder 'x' Foil.emptyNameMap
        Foil.lookupName (Foil.nameOf binder) nameMap `shouldBe` 'x'
        null (Foil.popNameBinder binder nameMap) `shouldBe` True

  describe "Data.IntSet over the sign bit (model: Data.Set)" $ do
    prop "toAscList is sorted across the sign boundary" $
      forAll (listOf genRawName) $ \xs ->
        IntSet.toAscList (IntSet.fromList xs)
          === Set.toAscList (Set.fromList xs)

    prop "findMin and findMax agree with the model" $
      forAll (listOf1 genRawName) $ \xs ->
        let s = IntSet.fromList xs
            m = Set.fromList xs
         in (IntSet.findMin s, IntSet.findMax s)
              === (Set.findMin m, Set.findMax m)

    prop "lookupLE agrees with the model" $
      forAll genRawName $ \k ->
        forAll (listOf genRawName) $ \xs ->
          IntSet.lookupLE k (IntSet.fromList xs)
            === Set.lookupLE k (Set.fromList xs)

    prop "split separates below and above across the sign boundary" $
      forAll genRawName $ \k ->
        forAll (listOf genRawName) $ \xs ->
          let (below, above) = IntSet.split k (IntSet.fromList xs)
           in sort (IntSet.toList below ++ IntSet.toList above)
                === sort [ x | x <- Set.toList (Set.fromList xs), x /= k ]
                .&&. all (< k) (IntSet.toList below)
                .&&. all (> k) (IntSet.toList above)

-- | The raw names bound by a list of binders, outermost first.
binderIds :: Foil.NameBinderList n l -> [Int]
binderIds Foil.NameBinderListEmpty = []
binderIds (Foil.NameBinderListCons binder binders) =
  Foil.nameId (Foil.nameOf binder) : binderIds binders
