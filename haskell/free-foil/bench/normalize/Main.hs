{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TypeFamilies     #-}

-- | Normalisation benchmark: full β-normalisation of untyped λ-terms over the
-- free foil, which is where the library's 'substitute' is put under pressure.
--
-- The workload is Church-numeral exponentiation. A Church numeral @n@ applied to
-- a Church numeral @m@ normalises to the Church numeral for @m^n@ (see
-- 'Control.Monad.Free.Foil.Example.nf'), so @'power' n m@ forces a number of
-- β-reductions that grows with @m^n@, each one a 'substitute' into a scoped
-- term. This is the same shape of workload as the free-foil module of
-- [lambda-n-ways](https://github.com/sweirich/lambda-n-ways) (Weirich's
-- benchmark suite), from the Free Foil paper.
--
-- There is no substitution or normalisation benchmark elsewhere in the package —
-- the @zipmatchk@ benchmark only exercises 'Control.Monad.Free.Foil.alphaEquiv' —
-- so this is the one that would show a change to term-building (a strict @AST@,
-- a substitution that skips unaffected subterms, and so on).
module Main (main) where

import           Test.Tasty.Bench

import           Control.Monad.Foil            (S (VoidS))
import           Control.Monad.Free.Foil       (pattern Var)
import           Control.Monad.Free.Foil.Example (Expr, churchN, nf', pattern AppE, pattern LamE)

-- | The size of a term, used to force the whole normal form (rather than just
-- its outermost constructor) without a 'Control.DeepSeq.NFData' instance.
sizeOf :: Expr n -> Int
sizeOf = \case
  Var{}       -> 1
  AppE f x    -> 1 + sizeOf f + sizeOf x
  LamE _ body -> 1 + sizeOf body

-- | @'power' n m@ is @m@ raised to the @n@: the Church numeral @n@ applied to
-- the Church numeral @m@, which normalises to the Church numeral for @m^n@.
power :: Int -> Int -> Expr VoidS
power n m = AppE (churchN n) (churchN m)

-- | Normalise, then walk the whole result so the benchmark forces it fully.
normalized :: Expr VoidS -> Int
normalized = sizeOf . nf'

main :: IO ()
main = defaultMain
  [ bgroup "nf of Church m^n"
      [ bench "8^2  = 64"   $ whnf normalized (power 2 8)
      , bench "4^3  = 64"   $ whnf normalized (power 3 4)
      , bench "12^2 = 144"  $ whnf normalized (power 2 12)
      , bench "2^8  = 256"  $ whnf normalized (power 8 2)
      , bench "2^10 = 1024" $ whnf normalized (power 10 2)
      ]
  ]
