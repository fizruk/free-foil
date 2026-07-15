{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | What the generic 'ZipMatchK' instance costs, and how that cost scales with
-- the size of the signature.
--
-- For each size, two structurally identical signatures differing only in how
-- their 'ZipMatchK' instance is obtained: @SigNG@ takes the generic default
-- (via "Generics.Kind"), @SigNH@ has the instance derived by
-- 'deriveZipMatchK'. Both are compared on 'alphaEquiv' of a large closed term
-- against itself, which is the worst case (no early exit) and the one a
-- typechecker actually hits.
--
-- The generic representation of a constructor is a chain of @L1@\/@R1@ wrappers
-- as long as the constructor's index, so a term built from constructors spread
-- across the whole signature — as a real language's terms are — should cost the
-- generic instance more the larger the signature is. The derived instance
-- compiles to a single @case@, and should not care.
module Main (main) where

import           Data.Bifunctor.TH
import           Test.Tasty.Bench

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil
import           Data.ZipMatchK
import           Data.ZipMatchK.TH       (deriveZipMatchK)
import           Generics.Kind.TH        (deriveGenericK)

import           Signature               (mkSig)

-- * Signatures of three sizes, twice over

mkSig "Sig2G" 2
mkSig "Sig2H" 2
mkSig "Sig10G" 10
mkSig "Sig10H" 10
mkSig "Sig44G" 44
mkSig "Sig44H" 44

deriveBifunctor ''Sig2G
deriveBifoldable ''Sig2G
deriveBitraversable ''Sig2G
deriveGenericK ''Sig2G
instance ZipMatchK Sig2G

deriveBifunctor ''Sig2H
deriveBifoldable ''Sig2H
deriveBitraversable ''Sig2H
deriveZipMatchK ''Sig2H

deriveBifunctor ''Sig10G
deriveBifoldable ''Sig10G
deriveBitraversable ''Sig10G
deriveGenericK ''Sig10G
instance ZipMatchK Sig10G

deriveBifunctor ''Sig10H
deriveBifoldable ''Sig10H
deriveBitraversable ''Sig10H
deriveZipMatchK ''Sig10H

deriveBifunctor ''Sig44G
deriveBifoldable ''Sig44G
deriveBitraversable ''Sig44G
deriveGenericK ''Sig44G
instance ZipMatchK Sig44G

deriveBifunctor ''Sig44H
deriveBifoldable ''Sig44H
deriveBitraversable ''Sig44H
deriveZipMatchK ''Sig44H

-- * A large closed term

-- | A closed term of the given depth: an application tree with a λ every other
-- level, cycling through the signature's application constructors so that the
-- whole signature is on the hot path.
mkTerm
  :: forall sig
   . (forall scope term. Int -> term -> term -> sig scope term)  -- ^ Application nodes.
  -> (forall scope term. scope -> sig scope term)                -- ^ λ-abstraction node.
  -> Int
  -> AST Foil.NameBinder sig Foil.VoidS
mkTerm app lam maxDepth = Foil.withFresh Foil.emptyScope $ \binder ->
  let scope = Foil.extendScope binder Foil.emptyScope
   in Node (lam (ScopedAST binder (go scope (Foil.nameOf binder) maxDepth)))
  where
    go :: Foil.Distinct n => Foil.Scope n -> Foil.Name n -> Int -> AST Foil.NameBinder sig n
    go _scope x 0 = Var x
    go scope x d
      | even d = Node (app d (go scope x (d - 1)) (go scope x (d - 1)))
      | otherwise = Foil.withFresh scope $ \binder ->
          let scope' = Foil.extendScope binder scope
           in Node (lam (ScopedAST binder (go scope' (Foil.sink x) (d - 1))))

-- | ~4000 leaves.
depth :: Int
depth = 24

main :: IO ()
main = defaultMain
  [ bgroup "alphaEquiv, term against itself"
      [ bgroup "2 constructors"
          [ bench "generic" $ whnf (alphaEquiv Foil.emptyScope t) t
          , bench "derived" $ whnf (alphaEquiv Foil.emptyScope u) u
          ]
      , bgroup "10 constructors"
          [ bench "generic" $ whnf (alphaEquiv Foil.emptyScope t10) t10
          , bench "derived" $ whnf (alphaEquiv Foil.emptyScope u10) u10
          ]
      , bgroup "44 constructors"
          [ bench "generic" $ whnf (alphaEquiv Foil.emptyScope t44) t44
          , bench "derived" $ whnf (alphaEquiv Foil.emptyScope u44) u44
          ]
      ]
  ]
  where
    t = mkTerm appSig2G lamSig2G depth
    u = mkTerm appSig2H lamSig2H depth
    t10 = mkTerm appSig10G lamSig10G depth
    u10 = mkTerm appSig10H lamSig10H depth
    t44 = mkTerm appSig44G lamSig44G depth
    u44 = mkTerm appSig44H lamSig44H depth
