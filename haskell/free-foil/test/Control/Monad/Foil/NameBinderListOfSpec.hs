{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
-- The raw types below only serve Template Haskell.
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- | The laws of 'Foil.CoSinkable', with the agreement of
-- 'Foil.nameBinderListOf' and 'Foil.withPattern', for the two ways to get an
-- instance that no other suite covers: 'deriveCoSinkable' and the generic
-- defaults of this package. Both pattern types consist of wildcards,
-- variables and pairs, so that the binders of a pattern come from fields at
-- different depths.
module Control.Monad.Foil.NameBinderListOfSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import qualified Control.Monad.Foil      as Foil
-- 'deriveCoSinkable' binds a variable named @rename@.
import           Control.Monad.Foil.Laws hiding (rename)
import           Control.Monad.Foil.TH   (deriveCoSinkable, mkFoilPattern)
import           Generics.Kind.TH        (deriveGenericK)

-- | A raw pattern, from which 'mkFoilPattern' and 'deriveCoSinkable' generate
-- 'FoilRawPattern' and its instance, which lists its binders directly.
newtype RawIdent = RawIdent String
data RawPattern
  = RawPatternWild
  | RawPatternVar RawIdent
  | RawPatternPair RawPattern RawPattern

mkFoilPattern ''RawIdent ''RawPattern
deriveCoSinkable ''RawIdent ''RawPattern

-- | A pattern whose instances are the generic defaults.
data GenericPattern (n :: Foil.S) (l :: Foil.S) where
  GenericPatternWild :: GenericPattern n n
  GenericPatternVar  :: Foil.NameBinder n l -> GenericPattern n l
  GenericPatternPair :: GenericPattern n i -> GenericPattern i l -> GenericPattern n l

deriveGenericK ''GenericPattern
instance Foil.SinkableK GenericPattern
instance Foil.HasNameBinders GenericPattern
instance Foil.CoSinkable GenericPattern

spec :: Spec
spec = do
  describe "a pattern from deriveCoSinkable" $
    coSinkableSpec rawPatternNames genRawPattern extensionByCoercion
  describe "a pattern with the generic defaults" $ do
    coSinkableSpec genericPatternNames genGenericPattern extensionByCoercion
    it "gnameBinderListOf lists the binders in the order of withPattern" $
      forAllShow (genPatternCase genGenericPattern Inclusions) (showPatternCase genericPatternNames) $
        \(PatternCase _ p) ->
          nameBinderListNames (Foil.gnameBinderListOf p) === patternRawNames p

-- | The shape of a pattern: where the wildcards, variables and pairs are. This
-- follows the generators of "Control.Monad.Free.Foil.TH.PatternTypesSpec".
data Shape = Wildcard | Variable | Pair Shape Shape

-- | A shape of nesting depth at most @d@.
genShape :: Int -> Gen Shape
genShape d = frequency $
  [ (1, pure Wildcard), (3, pure Variable) ] ++
  [ (2, Pair <$> genShape (d - 1) <*> genShape (d - 1)) | d > 0 ]

-- | A pattern of a random shape, built with the given constructors.
genShaped
  :: forall p. Foil.CoSinkable p
  => (forall n. p n n)
  -> (forall n l. Foil.NameBinder n l -> p n l)
  -> (forall n i l. p n i -> p i l -> p n l)
  -> GenPattern p
genShaped wild var pair ctx = withCtx ctx $ \scope -> do
  shape <- genShape 2
  go shape scope
  where
    go :: Foil.Distinct m => Shape -> Foil.Scope m -> Gen (PatIn p m)
    go shape scope = case shape of
      Wildcard -> pure (PatIn wild)
      Variable -> withHintedBinder scope (pure . PatIn . var)
      Pair left right -> do
        PatIn l <- go left scope
        PatIn r <- go right (Foil.extendScopePattern l scope)
        pure (PatIn (pair l r))

rawPatternNames :: PatternNames FoilRawPattern
rawPatternNames = \case
  FoilRawPatternWild     -> []
  FoilRawPatternVar b    -> [Foil.nameId (Foil.nameOf b)]
  FoilRawPatternPair l r -> rawPatternNames l ++ rawPatternNames r

genRawPattern :: GenPattern FoilRawPattern
genRawPattern = genShaped FoilRawPatternWild FoilRawPatternVar FoilRawPatternPair

genericPatternNames :: PatternNames GenericPattern
genericPatternNames = \case
  GenericPatternWild     -> []
  GenericPatternVar b    -> [Foil.nameId (Foil.nameOf b)]
  GenericPatternPair l r -> genericPatternNames l ++ genericPatternNames r

genGenericPattern :: GenPattern GenericPattern
genGenericPattern = genShaped GenericPatternWild GenericPatternVar GenericPatternPair
