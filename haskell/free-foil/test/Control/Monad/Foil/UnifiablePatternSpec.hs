{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | The default 'Foil.unifyPatterns' compares two patterns only up to their
-- binders: it flattens both to a 'Foil.NameBinderList' and unifies those. This
-- module pins down what that does /not/ distinguish, because the default is what
-- every client gets from an empty instance, and because two of its consequences
-- are surprising the first time they are met.
--
-- Since α-equivalence is defined in terms of 'Foil.unifyPatterns', these are also
-- statements about which terms the library considers α-equivalent.
--
-- None of this is a defect. What the body of a binding construct can refer to is
-- exactly the pattern's binders, in order, so for most languages the default is
-- the intended notion. It is a defect only for a language whose patterns carry
-- semantically relevant data — a constructor name in a @match@ branch, say — and
-- such a language should write 'Foil.unifyPatterns' by hand.
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
spec = describe "the default unifyPatterns" $ do
  it "ignores the constructor, so different constructors with equal binders unify" $
    -- The consequence worth knowing: for a pattern type whose constructors mean
    -- different things -- the branches of a @match@, say -- the default calls two
    -- of them equal, and no type error says so.
    Foil.withFresh Foil.emptyScope (\x ->
      unifiesWithoutRenaming (DemoVar x) (DemoBox x))
      `shouldBe` True

  it "ignores non-binding fields, whatever their values" $
    Foil.withFresh Foil.emptyScope (\x ->
      unifiesWithoutRenaming (DemoLabel "left" x) (DemoLabel "right" x))
      `shouldBe` True

  it "ignores nesting, so (x, (y, z)) unifies with ((x, y), z)" $
    -- Both flatten to the same three binders in the same order.
    withThreeBinders (\x y z ->
      unifiesWithoutRenaming
        (DemoPair (DemoVar x) (DemoPair (DemoVar y) (DemoVar z)))
        (DemoPair (DemoPair (DemoVar x) (DemoVar y)) (DemoVar z)))
      `shouldBe` True

  it "still tells apart patterns binding different numbers of names" $
    -- The default is not vacuous: the binders themselves are compared. This case
    -- used to throw 'PatternMatchFail', because the 'NameBinderList' instance had
    -- no case for lists of unequal length and this module disables
    -- @-Wincomplete-patterns@.
    withThreeBinders (\x y _z ->
      unifiesWithoutRenaming
        (DemoVar x)
        (DemoPair (DemoVar x) (DemoVar y)))
      `shouldBe` False
