{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Blocks: extension-within-a-range evidence, disjoint union, re-attachment.
module Control.Monad.Foil.BlocksSpec (spec) where

import           Data.Maybe                  (isJust)
import           Test.Hspec

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Foil.Blocks
import           Control.Monad.Foil.Internal (NameRange (..),
                                              rawNameBinderList)

-- | The raw names of a scope, in ascending order.
scopeIds :: Foil.Scope n -> [Int]
scopeIds = map Foil.nameId . Foil.nameSetToList . Foil.scopeToNameSet

ra, rb :: NameRange
ra = NameRange 100 199
rb = NameRange 200 299

spec :: Spec
spec = do
  describe "extWithinStep" $ do
    it "accepts a binder allocated inside the range" $
      Foil.withFreshIn ra Foil.emptyScope $ \b ->
        fmap extWithinRanges (extWithinStep b (extWithinRefl ra))
          `shouldBe` Just [ra]

    it "rejects a binder allocated outside the range" $
      Foil.withFresh Foil.emptyScope $ \b ->  -- allocates the name 0
        case extWithinStep b (extWithinRefl ra) of
          Nothing -> pure () :: IO ()
          Just _  -> expectationFailure "a name escaped the reservation"

  describe "withExtendScopeRange" $ do
    it "hands back consecutive binders, the scope, and the evidence" $
      case withExtendScopeRange Foil.emptyScope ra 3 $ \scope binders ext ->
             (scopeIds scope, rawNameBinderList binders, extWithinRanges ext) of
        Just result -> result `shouldBe` ([100, 101, 102], [100, 101, 102], [ra])
        Nothing     -> expectationFailure "the range was refused"

    it "refuses a range the scope already touches" $
      Foil.withFreshIn ra Foil.emptyScope $ \b ->
        let scope = Foil.extendScope b Foil.emptyScope
         in withExtendScopeRange scope ra 1 (\_ _ _ -> ()) `shouldBe` Nothing

    it "refuses more names than the range holds" $
      withExtendScopeRange Foil.emptyScope (NameRange 0 1) 3 (\_ _ _ -> ())
        `shouldBe` Nothing

  describe "withFreshInBlock" $
    it "allocates from the range, stepping the evidence in the same motion" $
      withFreshInBlock (beginBlock (NameRange 7 9)) Foil.emptyScope $ \b1 block1 ->
        withFreshInBlock block1 (Foil.extendScope b1 Foil.emptyScope) $ \b2 block2 -> do
          Foil.nameId (Foil.nameOf b1) `shouldBe` 7
          Foil.nameId (Foil.nameOf b2) `shouldBe` 8
          extWithinRanges (blockExt block2) `shouldBe` [NameRange 7 9]

  describe "composeExtWithin" $ do
    it "collects a chain's reservations exactly, coalescing adjacent ones" $ do
      extWithinRanges
        (composeExtWithin (extWithinRefl (NameRange 0 9)) (extWithinRefl (NameRange 30 39)))
        `shouldBe` [NameRange 0 9, NameRange 30 39]
      extWithinRanges
        (composeExtWithin (extWithinRefl (NameRange 0 9)) (extWithinRefl (NameRange 10 19)))
        `shouldBe` [NameRange 0 19]

    it "links two chains whose stripes interleave" $
      -- Chains {10-19, 30-39} and {20-29, 40-49}: the convex hulls overlap,
      -- the reservations do not. This is the diamond-of-chains shape that a
      -- single-range evidence could not link.
      let linked =
            withExtendScopeRange Foil.emptyScope (NameRange 10 19) 1 $ \s1 _ e1 ->
              withExtendScopeRange s1 (NameRange 30 39) 1 $ \s2 _ e2 ->
                withExtendScopeRange Foil.emptyScope (NameRange 20 29) 1 $ \t1 _ f1 ->
                  withExtendScopeRange t1 (NameRange 40 49) 1 $ \t2 _ f2 ->
                    withDisjointUnion (composeExtWithin e1 e2) (composeExtWithin f1 f2)
                      s2 t2 (\s _ _ -> scopeIds s)
       in linked `shouldBe` Just (Just (Just (Just (Just [10, 20, 30, 40]))))

  describe "withDisjointUnion" $ do
    it "links two units over a shared import scope" $
      Foil.withFresh Foil.emptyScope $ \bi ->  -- the shared import, name 0
        let c = Foil.extendScope bi Foil.emptyScope
            linked =
              withExtendScopeRange c ra 2 $ \sa _ ea ->
                withExtendScopeRange c rb 1 $ \sb _ eb ->
                  withDisjointUnion ea eb sa sb (\s _ _ -> scopeIds s)
         in linked `shouldBe` Just (Just (Just [0, 100, 101, 200]))

    it "refuses overlapping reservations" $
      let linked =
            withExtendScopeRange Foil.emptyScope ra 2 $ \sa _ ea ->
              withExtendScopeRange Foil.emptyScope ra 1 $ \sb _ eb ->
                withDisjointUnion ea eb sa sb (\s _ _ -> scopeIds s)
       in linked `shouldBe` Just (Just Nothing)

    it "extends both sides' maps to the union" $
      let looked =
            withExtendScopeRange Foil.emptyScope ra 1 $ \sa bsa ea ->
              withExtendScopeRange Foil.emptyScope rb 1 $ \sb bsb eb ->
                let m1 = Foil.addNameBinderList bsa ["a"] Foil.emptyNameMap
                    m2 = Foil.addNameBinderList bsb ["b"] Foil.emptyNameMap
                 in case (Foil.namesOfPattern bsa, Foil.namesOfPattern bsb) of
                      ([x1], [x2]) ->
                        withDisjointUnion ea eb sa sb $ \_scope union _ext ->
                          let u = unionNameMaps union m1 m2
                           in ( Foil.lookupName (Foil.sink x1) u
                              , Foil.lookupName (Foil.sink x2) u
                              )
                      _ -> Nothing
       in looked `shouldBe` Just (Just (Just ("a", "b")))

  describe "checkScopeUnion" $ do
    it "witnesses the union and nothing else" $
      let checked =
            withExtendScopeRange Foil.emptyScope ra 1 $ \sa _ ea ->
              withExtendScopeRange Foil.emptyScope rb 1 $ \sb _ eb ->
                withDisjointUnion ea eb sa sb $ \scope _ _ ->
                  ( isJust (checkScopeUnion sa sb scope)
                  , isJust (checkScopeUnion sa sa scope)  -- misses b's delta
                  )
       in checked `shouldBe` Just (Just (Just (True, False)))

  describe "checkExtScope" $ do
    it "mints evidence for a subset" $
      case withExtendScopeRange Foil.emptyScope ra 2 $ \sa _ _ ->
             isJust (checkExtScope Foil.emptyScope sa) of
        Just ok -> ok `shouldBe` True
        Nothing -> expectationFailure "the range was refused"

    it "refuses a non-extension" $
      let checked =
            withExtendScopeRange Foil.emptyScope ra 1 $ \sa _ _ ->
              withExtendScopeRange Foil.emptyScope rb 1 $ \sb _ _ ->
                isJust (checkExtScope sa sb)
       in checked `shouldBe` Just (Just False)
