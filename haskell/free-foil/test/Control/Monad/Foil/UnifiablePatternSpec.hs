{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | The default 'Foil.unifyPatterns' is 'Foil.gunifyPatterns': two patterns
-- unify when they consist of the same constructors, nested in the same way, and
-- their binders are then paired in order. This module pins down what it tells
-- apart and what it does not (non-binding fields), since the default is what
-- every client gets from an empty instance.
--
-- It also pins down 'Foil.unifyPatternBinders', which compares only the number
-- and order of binders. That was the default up to version 0.4.0, and it is
-- still what a pattern type without 'GenericK' can take. Two of its
-- consequences are surprising the first time they are met.
--
-- Since α-equivalence is defined in terms of 'Foil.unifyPatterns', these are also
-- statements about which terms the library considers α-equivalent.
module Control.Monad.Foil.UnifiablePatternSpec (spec) where

import           Test.Hspec

import qualified Control.Monad.Foil as Foil
import           Generics.Kind.TH   (deriveGenericK)

-- | A pattern type with just enough structure to observe the default:
-- two constructors binding one name each, a nesting constructor, and a
-- constructor carrying a non-binding field.
data DemoPattern (n :: Foil.S) (l :: Foil.S) where
  DemoVar   :: Foil.NameBinder n l -> DemoPattern n l
  DemoBox   :: Foil.NameBinder n l -> DemoPattern n l
  DemoPair  :: DemoPattern n i -> DemoPattern i l -> DemoPattern n l
  DemoLabel :: String -> Foil.NameBinder n l -> DemoPattern n l

-- The configuration every client uses: derive the generic representation, then
-- take all four instances from their defaults.
deriveGenericK ''DemoPattern
instance Foil.SinkableK DemoPattern
instance Foil.HasNameBinders DemoPattern
instance Foil.CoSinkable DemoPattern
instance Foil.UnifiablePattern DemoPattern

-- | The same pattern type, comparing only binders with
-- 'Foil.unifyPatternBinders'.
data BinderPattern (n :: Foil.S) (l :: Foil.S) where
  BinderVar   :: Foil.NameBinder n l -> BinderPattern n l
  BinderBox   :: Foil.NameBinder n l -> BinderPattern n l
  BinderPair  :: BinderPattern n i -> BinderPattern i l -> BinderPattern n l
  BinderLabel :: String -> Foil.NameBinder n l -> BinderPattern n l

deriveGenericK ''BinderPattern
instance Foil.SinkableK BinderPattern
instance Foil.HasNameBinders BinderPattern
instance Foil.CoSinkable BinderPattern
instance Foil.UnifiablePattern BinderPattern where
  unifyPatterns = Foil.unifyPatternBinders

-- | Do the two patterns unify, with or without a renaming?
unifies
  :: (Foil.UnifiablePattern pattern, Foil.Distinct n)
  => pattern n l -> pattern n r -> Bool
unifies l r =
  case Foil.unifyPatterns l r of
    Foil.NotUnifiable -> False
    _                 -> True

-- | Do the two patterns unify with no renaming required? This is the observation
-- α-equivalence makes, phrased in the public API.
unifiesWithoutRenaming
  :: (Foil.UnifiablePattern pattern, Foil.Distinct n)
  => pattern n l -> pattern n r -> Bool
unifiesWithoutRenaming l r =
  case Foil.unifyPatterns l r of
    Foil.SameNameBinders{} -> True
    _                      -> False

-- | Run a continuation with three binders nested in 'Foil.emptyScope'.
withThreeBinders
  :: (forall i1 i2 l.
        Foil.NameBinder Foil.VoidS i1
     -> Foil.NameBinder i1 i2
     -> Foil.NameBinder i2 l
     -> r)
  -> r
withThreeBinders cont =
  Foil.withFresh Foil.emptyScope $ \x ->
    case Foil.assertDistinct x of
      Foil.Distinct ->
        Foil.withFresh (Foil.extendScope x Foil.emptyScope) $ \y ->
          case Foil.assertDistinct y of
            Foil.Distinct ->
              Foil.withFresh (Foil.extendScope y (Foil.extendScope x Foil.emptyScope)) $ \z ->
                cont x y z

spec :: Spec
spec = do
  defaultSpec
  binderSpec

-- | What the default 'Foil.unifyPatterns' tells apart: constructors and their
-- nesting, as well as binders.
defaultSpec :: Spec
defaultSpec = describe "the default unifyPatterns" $ do
  it "tells apart different constructors with equal binders" $
    Foil.withFresh Foil.emptyScope (\x ->
      unifies (DemoVar x) (DemoBox x))
      `shouldBe` False

  it "tells apart different constructors under a common one" $
    withThreeBinders (\x y _z ->
      unifies
        (DemoPair (DemoVar x) (DemoVar y))
        (DemoPair (DemoBox x) (DemoVar y)))
      `shouldBe` False

  it "tells apart (x, (y, z)) and ((x, y), z)" $
    withThreeBinders (\x y z ->
      unifies
        (DemoPair (DemoVar x) (DemoPair (DemoVar y) (DemoVar z)))
        (DemoPair (DemoPair (DemoVar x) (DemoVar y)) (DemoVar z)))
      `shouldBe` False

  it "tells apart patterns binding different numbers of names" $
    withThreeBinders (\x y _z ->
      unifies
        (DemoVar x)
        (DemoPair (DemoVar x) (DemoVar y)))
      `shouldBe` False

  it "ignores non-binding fields, whatever their values" $
    Foil.withFresh Foil.emptyScope (\x ->
      unifiesWithoutRenaming (DemoLabel "left" x) (DemoLabel "right" x))
      `shouldBe` True

  it "pairs the binders of two patterns of one shape in order" $
    -- (x0, x1) against (x1, x0): the right binders are renamed to the left
    -- ones position by position, so x1 goes to x0 and x0 to x1.
    withThreeBinders (\x y _z ->
      Foil.withRefreshed Foil.emptyScope (Foil.nameOf y) (\x' ->
        Foil.withRefreshed (Foil.extendScope x' Foil.emptyScope) (Foil.nameOf x) (\y' ->
          case Foil.unifyPatterns
                 (DemoPair (DemoVar x) (DemoVar y))
                 (DemoPair (DemoVar x') (DemoVar y')) of
            Foil.RenameRightNameBinder _ rename ->
              map (Foil.nameId . Foil.fromNameBinderRenaming rename)
                  [Foil.sink (Foil.nameOf x'), Foil.nameOf y']
            _ -> [])))
      `shouldBe` [0, 1]

-- | What 'Foil.unifyPatternBinders' does not tell apart.
binderSpec :: Spec
binderSpec = describe "unifyPatternBinders" $ do
  it "ignores the constructor, so different constructors with equal binders unify" $
    -- The consequence worth knowing: for a pattern type whose constructors mean
    -- different things -- the branches of a @match@, say -- this calls two of
    -- them equal, and no type error says so.
    Foil.withFresh Foil.emptyScope (\x ->
      unifiesWithoutRenaming (BinderVar x) (BinderBox x))
      `shouldBe` True

  it "ignores non-binding fields, whatever their values" $
    Foil.withFresh Foil.emptyScope (\x ->
      unifiesWithoutRenaming (BinderLabel "left" x) (BinderLabel "right" x))
      `shouldBe` True

  it "ignores nesting, so (x, (y, z)) unifies with ((x, y), z)" $
    -- Both flatten to the same three binders in the same order.
    withThreeBinders (\x y z ->
      unifiesWithoutRenaming
        (BinderPair (BinderVar x) (BinderPair (BinderVar y) (BinderVar z)))
        (BinderPair (BinderPair (BinderVar x) (BinderVar y)) (BinderVar z)))
      `shouldBe` True

  it "still tells apart patterns binding different numbers of names" $
    -- The binders themselves are compared. This case used to throw
    -- 'PatternMatchFail', because the 'NameBinderList' instance had no case
    -- for lists of unequal length and "Control.Monad.Foil.Internal" disables
    -- @-Wincomplete-patterns@.
    withThreeBinders (\x y _z ->
      unifiesWithoutRenaming
        (BinderVar x)
        (BinderPair (BinderVar x) (BinderVar y)))
      `shouldBe` False
