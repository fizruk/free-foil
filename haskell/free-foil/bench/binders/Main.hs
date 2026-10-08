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
-- Each pattern type is measured twice. At a known type, a call can be
-- specialised. Through 'SomePattern', the 'Foil.CoSinkable' dictionary is
-- passed at run time, as it is in code that is polymorphic in the pattern
-- type, such as a generic typechecker.
module Main (main) where

import           Data.Bifunctor.TH
import           Test.Tasty.Bench

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Foil.TH   (deriveCoSinkable, mkFoilPattern)
import           Control.Monad.Free.Foil
import           Data.ZipMatchK.TH       (deriveZipMatchK)
import           Generics.Kind.TH        (deriveGenericK)

-- | A pattern of two binders, with every instance taken from its generic
-- default, as a client that derives 'GenericK' gets it.
data PairPattern (n :: Foil.S) (l :: Foil.S) where
  PairPattern :: Foil.NameBinder n i -> Foil.NameBinder i l -> PairPattern n l

deriveGenericK ''PairPattern
instance Foil.SinkableK PairPattern
instance Foil.HasNameBinders PairPattern
instance Foil.CoSinkable PairPattern
instance Foil.UnifiablePattern PairPattern

-- | A pattern of one binder with the instance that 'deriveCoSinkable'
-- generates, as in a language generated from a BNFC grammar.
newtype RawIdent = RawIdent String
data RawPattern = RawPatternVar RawIdent

mkFoilPattern ''RawIdent ''RawPattern
deriveCoSinkable ''RawIdent ''RawPattern

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
    let pair = PairPattern b1 b2
        var = FoilRawPatternVar b1
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
              , bgroup "generic pattern of 2"
                  [ bench "known type"   $ whnf (size . Foil.nameBinderListOf) pair
                  , bench "a dictionary" $ whnf listedSome (SomePattern pair)
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
