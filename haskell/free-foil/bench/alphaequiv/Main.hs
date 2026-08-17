{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | What the rename branches of 'alphaEquivScoped' cost.
--
-- The zipmatchk benchmark compares a term against itself, so the binders
-- always coincide and 'unifyPatternsIn' answers 'SameNameBinders': the
-- fast path, no renaming. This benchmark forces the other branches: @t2@
-- is α-equivalent to @t1@ but every binder carries a different raw name
-- (it is built under a dummy binder and then 'unsinkAST'-ed back to the
-- empty scope), so every level takes a Rename* branch. An eager
-- implementation materialised a renamed copy of the whole remaining body
-- per level, which is quadratic in the depth of the chain; with the
-- renaming threaded down the recursion, all three columns must stay
-- linear and within a small factor of one another.
module Main (main) where

import           Data.Bifunctor.TH
import           Data.Maybe              (fromMaybe)
import           Test.Tasty.Bench

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil
import           Data.ZipMatchK.TH       (deriveZipMatchK)

data LamSig scope term
  = App term term
  | Lam scope
  deriving (Functor, Foldable, Traversable)

deriveBifunctor ''LamSig
deriveBifoldable ''LamSig
deriveBitraversable ''LamSig
deriveZipMatchK ''LamSig

type Term = AST Foil.NameBinder LamSig

-- | λx1. λx2. … λxn. xn, allocated in the given scope.
chainIn :: Foil.Distinct n => Foil.Scope n -> Int -> Foil.Name n -> Term n
chainIn _scope 0 x = Var x
chainIn scope k _x = Foil.withFresh scope $ \binder ->
  let scope' = Foil.extendScope binder scope
   in Node (Lam (ScopedAST binder (chainIn scope' (k - 1) (Foil.nameOf binder))))

-- | The chain over the empty scope: binders 0, 1, …, n−1.
plain :: Int -> Term Foil.VoidS
plain n = Foil.withFresh Foil.emptyScope $ \b0 ->
  let scope0 = Foil.extendScope b0 Foil.emptyScope
   in Node (Lam (ScopedAST b0 (chainIn scope0 (n - 1) (Foil.nameOf b0))))

-- | The same chain built under one dummy binder and cut back down:
-- binders 1, 2, …, n, so every level differs from 'plain' by exactly one.
shifted :: Int -> Term Foil.VoidS
shifted n = Foil.withFresh Foil.emptyScope $ \dummy ->
  let scope1 = Foil.extendScope dummy Foil.emptyScope
      t = Foil.withFresh scope1 $ \b1 ->
            let scope2 = Foil.extendScope b1 scope1
             in Node (Lam (ScopedAST b1 (chainIn scope2 (n - 1) (Foil.nameOf b1))))
   in fromMaybe (error "the chain uses the dummy binder")
        (unsinkAST Foil.emptyScope t)

sized :: Int -> Benchmark
sized n =
  let t1 = plain n
      t2 = shifted n
   in if not (alphaEquiv Foil.emptyScope t1 t2)
        then error "the two chains are not alpha-equivalent"
        else bgroup (show n <> " nested binders")
               [ bench "same binders (fast path)" $
                   whnf (alphaEquiv Foil.emptyScope t1) t1
               , bench "all binders differ (rename path)" $
                   whnf (alphaEquiv Foil.emptyScope t1) t2
               , bench "all binders differ, alphaEquivRefreshed" $
                   whnf (alphaEquivRefreshed Foil.emptyScope t1) t2
               ]

main :: IO ()
main = defaultMain [ sized n | n <- [250, 500, 1000, 2000] ]
