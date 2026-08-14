{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A pattern may carry fields indexed by its own scope, the standard example
-- being a telescope, where each step has a type in the scope the steps before
-- it extend to. 'Foil.withPattern' rebuilds a pattern at an /unrelated/ ambient
-- scope, and hands the instance no renaming for such a field: the only thing
-- relating the two scopes is the pair of binders each step produces.
--
-- 'Foil.PatternTransport' is that missing renaming. This module pins down what
-- it has to do, on the smallest pattern that can tell the difference: a chain
-- of binders where each step carries a name from the scope before it, so that a
-- payload can point at a binder the traversal is about to refresh.
--
-- The two halves are: a payload naming something the pattern does not bind is
-- left alone, and a payload naming one of the pattern's own binders follows
-- that binder when it is refreshed.
--
-- The second half is what the generic implementation of 'Foil.withPattern'
-- cannot do, since it replaces the binders and leaves the other fields as they
-- stand. That is now refused rather than answered wrongly: deriving the
-- instances for 'Chain' below — @deriveGenericK ''Chain@ and then an empty
-- @HasNameBinders@ instance — is a type error naming the offending field,
--
-- > A field of the binder/pattern is indexed by a Foil scope
-- >   Foil.Name outerScope : S
--
-- so the refusal cannot be tested here, only recorded. Before it, the derived
-- route compiled and gave the binders @[3,4]@ with the payloads left at
-- @[0,1]@.
module Control.Monad.Foil.PatternTransportSpec (spec) where

import           Test.Hspec

import qualified Control.Monad.Foil as Foil

-- | A chain of binders, each carrying a name in the scope before it.
data Chain (n :: Foil.S) (l :: Foil.S) where
  ChainEmpty :: Chain n n
  ChainCons  :: Foil.Name n -> Foil.NameBinder n i -> Chain i l -> Chain n l

instance Foil.CoSinkable Chain where
  coSinkabilityProof rename ChainEmpty cont = cont rename ChainEmpty
  coSinkabilityProof rename (ChainCons payload binder rest) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      Foil.coSinkabilityProof rename' rest $ \rename'' rest' ->
        cont rename'' (ChainCons (rename payload) binder' rest')

  withPattern
    :: forall f o n l r. Foil.Distinct o
    => (forall x y z r'. Foil.Distinct z
          => Foil.Scope z
          -> Foil.NameBinder x y
          -> (forall z'. Foil.DExt z z' => f x y z z' -> Foil.NameBinder z z' -> r')
          -> r')
    -> (forall x z z'. Foil.DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (Foil.DExt z z', Foil.DExt z' z'')
          => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Foil.Scope o
    -> Chain n l
    -> (forall o'. Foil.DExt o o' => f n l o o' -> Chain o o' -> r)
    -> r
  withPattern withBinder unit comp = go Foil.verbatimTransport
    where
      go :: forall n' l' o' r'. Foil.Distinct o'
         => Foil.PatternTransport n' o'
         -> Foil.Scope o'
         -> Chain n' l'
         -> (forall o''. Foil.DExt o' o'' => f n' l' o' o'' -> Chain o' o'' -> r')
         -> r'
      go _transport _scope ChainEmpty cont = cont unit ChainEmpty
      go transport scope (ChainCons payload binder rest) cont =
        withBinder scope binder $ \fbinder binder' ->
          go (Foil.transportUnderBinder transport binder binder')
             (Foil.extendScope binder' scope)
             rest $ \frest rest' ->
            cont (comp fbinder frest)
              (ChainCons (Foil.transportPayload transport payload) binder' rest')

-- | The result of processing one binder, when there is nothing to carry.
data NoInfo (x :: Foil.S) (y :: Foil.S) (z :: Foil.S) (z' :: Foil.S) = NoInfo

-- | Refresh a chain against an ambient scope, renaming only the binders that
-- clash with it. This is 'Foil.withRefreshedPattern' without the substitution.
refreshChain
  :: Foil.Distinct o
  => Foil.Scope o
  -> Chain n l
  -> (forall o'. Foil.DExt o o' => Chain o o' -> r)
  -> r
refreshChain scope chain cont =
  Foil.withPattern
    (\scope' binder k ->
      Foil.withRefreshed scope' (Foil.nameOf binder) (k NoInfo))
    NoInfo
    (\NoInfo NoInfo -> NoInfo)
    scope
    chain
    (\NoInfo chain' -> cont chain')

-- | A chain of two binders, allocated under one binder that it does not bind.
--
-- The binders are the raw names 1 and 2. The first payload is the raw name 0,
-- which the chain does not bind; the second is the raw name 1, which it does.
withChain
  :: (forall i l. Foil.Distinct i => Chain i l -> r) -> r
withChain cont =
  Foil.withFresh Foil.emptyScope $ \b0 ->
    let scope0 = Foil.extendScope b0 Foil.emptyScope
     in Foil.withFresh scope0 $ \b1 ->
          let scope1 = Foil.extendScope b1 scope0
           in Foil.withFresh scope1 $ \b2 ->
                cont (ChainCons (Foil.nameOf b0) b1
                       (ChainCons (Foil.nameOf b1) b2 ChainEmpty))

-- | A scope holding the raw names 0, 1 and 2, so that both of the chain's
-- binders clash with it.
withClashingScope :: (forall o. Foil.Distinct o => Foil.Scope o -> r) -> r
withClashingScope cont =
  Foil.withFresh Foil.emptyScope $ \b0 ->
    let scope0 = Foil.extendScope b0 Foil.emptyScope
     in Foil.withFresh scope0 $ \b1 ->
          let scope1 = Foil.extendScope b1 scope0
           in Foil.withFresh scope1 $ \b2 ->
                cont (Foil.extendScope b2 scope1)

binders :: Chain n l -> [Foil.RawName]
binders ChainEmpty                  = []
binders (ChainCons _ binder rest)   = Foil.nameId (Foil.nameOf binder) : binders rest

payloads :: Chain n l -> [Foil.RawName]
payloads ChainEmpty                 = []
payloads (ChainCons payload _ rest) = Foil.nameId payload : payloads rest

spec :: Spec
spec = do
  describe "a pattern with scoped payloads" $ do
    it "is built with the binders and payloads the tests expect" $
      withChain $ \chain ->
        (binders chain, payloads chain) `shouldBe` ([1, 2], [0, 1])

    it "keeps its payloads when no binder is refreshed" $
      withChain $ \chain ->
        refreshChain Foil.emptyScope chain $ \chain' ->
          (binders chain', payloads chain') `shouldBe` ([1, 2], [0, 1])

    it "carries a payload along the binder it names when that binder moves" $
      -- Both binders clash and are refreshed to 3 and 4. The payload naming the
      -- chain's own first binder has to become 3; the payload naming something
      -- outside the chain stays 0. Coercing the payloads instead, as the
      -- default implementation does, would leave the first one at 1.
      withChain $ \chain ->
        withClashingScope $ \scope ->
          refreshChain scope chain $ \chain' ->
            (binders chain', payloads chain') `shouldBe` ([3, 4], [0, 3])

  describe "the traversals that never refresh" $
    it "see the binders without walking the payloads" $
      withChain $ \chain ->
        map Foil.nameId (Foil.namesOfPattern chain) `shouldBe` binders chain
