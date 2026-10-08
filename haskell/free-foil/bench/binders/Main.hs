{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
-- The raw types below only serve Template Haskell.
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | What it costs to list the binders of a pattern with
-- 'Foil.nameBinderListOf', and the operations that go through it:
-- 'Foil.addSubstPattern', 'Foil.unsinkNameSet' (in 'supportOf') and the
-- default 'Foil.unifyPatterns' (in 'alphaEquiv').
--
-- The pattern types cover each way to get a 'Foil.CoSinkable' instance: the
-- library's own instances (with 'Telescope'), 'deriveCoSinkable',
-- 'mkFreeFoil', instances written by hand and the generic default.
--
-- Each pattern type is measured twice. At a known type, a call can be
-- specialised. Through 'SomePattern', the 'Foil.CoSinkable' dictionary is
-- passed at run time, as it is in code that is polymorphic in the pattern
-- type, such as a generic typechecker.
module Main (main) where

import           Data.Bifunctor.TH
import           Test.Tasty.Bench

import qualified Control.Monad.Foil            as Foil
import qualified Control.Monad.Foil.Example    as Example
import           Control.Monad.Foil.Telescope  (Telescope (..))
import           Control.Monad.Foil.TH         (deriveCoSinkable, mkFoilPattern)
import           Control.Monad.Free.Foil
import           Data.ZipMatchK.TH       (deriveZipMatchK)
import           Generics.Kind.TH        (deriveGenericK)

import           Generated               (FFBPattern (..))

-- | A pattern of two binders, with every instance taken from its generic
-- default, as a client that derives 'GenericK' gets it.
data PairPattern (n :: Foil.S) (l :: Foil.S) where
  PairPattern :: Foil.NameBinder n i -> Foil.NameBinder i l -> PairPattern n l

deriveGenericK ''PairPattern
instance Foil.SinkableK PairPattern
instance Foil.HasNameBinders PairPattern
instance Foil.CoSinkable PairPattern
instance Foil.UnifiablePattern PairPattern

-- | 'PairPattern' with 'Foil.gnameBinderListOf' for 'Foil.nameBinderListOf'.
data GPairPattern (n :: Foil.S) (l :: Foil.S) where
  GPairPattern :: Foil.NameBinder n i -> Foil.NameBinder i l -> GPairPattern n l

deriveGenericK ''GPairPattern
instance Foil.SinkableK GPairPattern
instance Foil.HasNameBinders GPairPattern
instance Foil.CoSinkable GPairPattern where
  nameBinderListOf = Foil.gnameBinderListOf

-- | A pattern of variables and pairs with the instance that
-- 'deriveCoSinkable' generates, as in a language generated from a BNFC grammar.
newtype RawIdent = RawIdent String
data RawPattern = RawPatternVar RawIdent | RawPatternPair RawPattern RawPattern

mkFoilPattern ''RawIdent ''RawPattern
deriveCoSinkable ''RawIdent ''RawPattern

-- | A pattern of two binders with 'Foil.withPattern' written by hand and no
-- other method.
data HandPair (n :: Foil.S) (l :: Foil.S) where
  HandPair :: Foil.NameBinder n i -> Foil.NameBinder i l -> HandPair n l

instance Foil.CoSinkable HandPair where
  coSinkabilityProof rename (HandPair x y) cont =
    Foil.coSinkabilityProof rename x $ \rename' x' ->
      Foil.coSinkabilityProof rename' y $ \rename'' y' ->
        cont rename'' (HandPair x' y')

  withPattern withBinder _unit comp scope (HandPair x y) cont =
    withBinder scope x $ \fx x' ->
      let scope' = Foil.extendScope x' scope
       in withBinder scope' y $ \fy y' ->
            cont (comp fx fy) (HandPair x' y') (Foil.extendScope y' scope')

-- | A copy of the pattern of "Language.LambdaPi.Impl.Foil" and its instance:
-- wildcards, variables and pairs, with a recursive 'Foil.withPattern' written
-- by hand.
data LPPattern (n :: Foil.S) (l :: Foil.S) where
  LPWildcard :: LPPattern n n
  LPVar      :: Foil.NameBinder n l -> LPPattern n l
  LPPair     :: LPPattern n i -> LPPattern i l -> LPPattern n l

instance Foil.CoSinkable LPPattern where
  coSinkabilityProof rename pattern cont =
    case pattern of
      LPWildcard -> cont rename LPWildcard
      LPVar x ->
        Foil.coSinkabilityProof rename x $ \rename' x' ->
          cont rename' (LPVar x')
      LPPair l r ->
        Foil.coSinkabilityProof rename l $ \rename' l' ->
          Foil.coSinkabilityProof rename' r $ \rename'' r' ->
            cont rename'' (LPPair l' r')

  withPattern withNameBinder id' combine scope pattern cont =
    case pattern of
      LPWildcard -> cont id' LPWildcard scope
      LPVar x    -> withNameBinder scope x $ \f x' ->
        cont f (LPVar x') (Foil.extendScope x' scope)
      LPPair l r -> Foil.withPattern withNameBinder id' combine scope l $ \fl l' scope' ->
        Foil.withPattern withNameBinder id' combine scope' r $ \fr r' scope'' ->
          cont (combine fl fr) (LPPair l' r') scope''

-- | A telescope of @k@ steps @(x1 : \\y. y) (x2 : x1) ... (xk : x(k-1))@,
-- with the terms of "Control.Monad.Foil.Example" for payloads.
withTelescope
  :: forall r. Int
  -> (forall l. Telescope () Example.Expr Foil.VoidS l -> r)
  -> r
withTelescope k cont =
  Foil.withFresh Foil.emptyScope $ \y ->
    Foil.withFresh Foil.emptyScope $ \x ->
      go (k - 1) (Foil.extendScope x Foil.emptyScope) (Foil.nameOf x) $ \rest ->
        cont (TelescopeCons () (Example.LamE y (Example.VarE (Foil.nameOf y))) x rest)
  where
    go :: Foil.Distinct n
       => Int -> Foil.Scope n -> Foil.Name n
       -> (forall l. Telescope () Example.Expr n l -> r) -> r
    go 0 _ _ cont' = cont' TelescopeEmpty
    go j scope prev cont' = Foil.withFresh scope $ \b ->
      go (j - 1) (Foil.extendScope b scope) (Foil.nameOf b) $ \rest ->
        cont' (TelescopeCons () (Example.VarE (Foil.sink prev)) b rest)

data LamSig scope term
  = App term term
  | Lam scope
  deriving (Functor, Foldable, Traversable)

deriveBifunctor ''LamSig
deriveBifoldable ''LamSig
deriveBitraversable ''LamSig
deriveZipMatchK ''LamSig

-- | A pattern whose 'Foil.CoSinkable' dictionary travels with it.
data SomePattern where
  SomePattern :: Foil.CoSinkable pattern => pattern Foil.VoidS l -> SomePattern

-- | The length of a list of binders, which forces its spine.
size :: Foil.NameBinderList n l -> Int
size = go 0
  where
    go :: Int -> Foil.NameBinderList n l -> Int
    go !acc Foil.NameBinderListEmpty         = acc
    go !acc (Foil.NameBinderListCons _ rest) = go (acc + 1) rest

-- | 'Foil.nameBinderListOf' through a dictionary. Not inlined, so that the
-- dictionary stays unknown at the call.
{-# NOINLINE listedSome #-}
listedSome :: SomePattern -> Int
listedSome (SomePattern pattern) = size (Foil.nameBinderListOf pattern)

-- | 'Foil.addSubstPattern' through a dictionary.
{-# NOINLINE substSome #-}
substSome :: [AST PairPattern LamSig Foil.VoidS] -> SomePattern -> Bool
substSome args (SomePattern pattern) =
  Foil.nullSubst (Foil.addSubstPattern Foil.identitySubst pattern args)

-- | A chain of λ-abstractions, each binding a pair of names, with a variable
-- bound by the outermost one at the bottom.
pairChain :: Int -> AST PairPattern LamSig Foil.VoidS
pairChain depth =
  withPair Foil.emptyScope $ \pattern x scope ->
    Node (Lam (ScopedAST pattern (go scope x (depth - 1))))
  where
    go :: Foil.Distinct n => Foil.Scope n -> Foil.Name n -> Int -> AST PairPattern LamSig n
    go _scope x 0 = Var x
    go scope x d = withPair scope $ \pattern _ scope' ->
      Node (Lam (ScopedAST pattern (go scope' (Foil.sink x) (d - 1))))

    withPair
      :: Foil.Distinct n
      => Foil.Scope n
      -> (forall l. Foil.DExt n l => PairPattern n l -> Foil.Name l -> Foil.Scope l -> r)
      -> r
    withPair scope cont =
      Foil.withFresh scope $ \b1 ->
        let scope1 = Foil.extendScope b1 scope
         in Foil.withFresh scope1 $ \b2 ->
              cont (PairPattern b1 b2) (Foil.sink (Foil.nameOf b1)) (Foil.extendScope b2 scope1)

main :: IO ()
main =
  Foil.withFresh Foil.emptyScope $ \b1 ->
  Foil.withFresh (Foil.extendScope b1 Foil.emptyScope) $ \b2 ->
  Foil.withFreshNameBinderList [(), (), (), ()] Foil.emptyScope Foil.emptyNameMap $ \_ list4 _ ->
  withTelescope 4 $ \tele4 ->
    let pair = PairPattern b1 b2
        var = FoilRawPatternVar b1
        thPair = FoilRawPatternPair (FoilRawPatternVar b1) (FoilRawPatternVar b2)
        ffPair = FFBPatternPair (FFBPatternVar b1) (FFBPatternVar b2)
        handPair = HandPair b1 b2
        lpPair = LPPair (LPVar b1) (LPVar b2)
        gpair = GPairPattern b1 b2
        args = [Node (App t t), t]
        t = pairChain 1
        chain = pairChain 1000
     in defaultMain
          [ bgroup "nameBinderListOf"
              [ bgroup "NameBinder"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) b1
                  , bench "a dictionary" $ whnf listedSome (SomePattern b1)
                  ]
              , bgroup "TH pattern of 1"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) var
                  , bench "a dictionary" $ whnf listedSome (SomePattern var)
                  ]
              , bgroup "NameBinderList of 4"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) list4
                  , bench "a dictionary" $ whnf listedSome (SomePattern list4)
                  ]
              , bgroup "deriveCoSinkable pair of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) thPair
                  , bench "a dictionary" $ whnf listedSome (SomePattern thPair)
                  ]
              , bgroup "mkFreeFoil pair of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) ffPair
                  , bench "a dictionary" $ whnf listedSome (SomePattern ffPair)
                  ]
              , bgroup "hand-written pair of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) handPair
                  , bench "a dictionary" $ whnf listedSome (SomePattern handPair)
                  ]
              , bgroup "lambda-pi pattern, pair of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) lpPair
                  , bench "a dictionary" $ whnf listedSome (SomePattern lpPair)
                  ]
              , bgroup "Telescope of 4"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) tele4
                  , bench "a dictionary" $ whnf listedSome (SomePattern tele4)
                  ]
              , bgroup "generic pattern of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) pair
                  , bench "a dictionary" $ whnf listedSome (SomePattern pair)
                  ]
              , bgroup "generic pattern of 2 with gnameBinderListOf"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) gpair
                  , bench "a dictionary" $ whnf listedSome (SomePattern gpair)
                  ]
              ]
          , bgroup "addSubstPattern, generic pattern of 2"
              [ bench "known type"   $
                  whnf (\p -> Foil.nullSubst (Foil.addSubstPattern Foil.identitySubst p args)) pair
              , bench "a dictionary" $ whnf (substSome args) (SomePattern pair)
              ]
          , bgroup "1000 nested generic patterns of 2"
              [ bench "alphaEquiv" $ whnf (alphaEquiv Foil.emptyScope chain) chain
              , bench "supportOf"  $ whnf (Foil.nameSetSize . supportOf) chain
              ]
          ]
