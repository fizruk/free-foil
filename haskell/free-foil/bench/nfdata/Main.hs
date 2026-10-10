{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE GADTs          #-}

-- | What it costs to force a term with 'rnf'.
--
-- Benchmarks force their results with 'rnf' (for example, through 'nf' of
-- tasty-bench), so the 'NFData' instance of 'AST' adds to every measurement
-- of a function that returns a term. The signature here takes the generic
-- 'NFData' instance, as user code usually does.
--
-- The workload is 100 random closed λ-terms of 4 to 32 nodes (about 1,850
-- nodes in total), comparable in size to the 100 normal forms of the
-- @random15@ corpus of [lambda-n-ways](https://github.com/sweirich/lambda-n-ways)
-- (Weirich's benchmark suite), and one random term of 20,000 nodes.
module Main (main) where

import           Control.DeepSeq   (NFData, force, rnf)
import           Control.Exception (evaluate)
import           Data.Bits         (shiftR)
import           Data.Word         (Word64)
import           GHC.Generics      (Generic)
import           Test.Tasty.Bench

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil

data LamSig scope term
  = App term term
  | Lam scope
  deriving (Generic, NFData)

type Term = AST Foil.NameBinder LamSig

-- | A λ-term with de Bruijn indices, generated first and then converted.
data Raw = RVar Int | RApp Raw Raw | RLam Raw

-- | The linear congruential generator of Knuth's MMIX.
next :: Word64 -> Word64
next g = g * 6364136223846793005 + 1442695040888963407

-- | A number below @k@, from the high bits of the state.
pick :: Word64 -> Int -> Int
pick g k = fromIntegral ((g `shiftR` 33) `mod` fromIntegral k)

-- | @'gen' d s g@ is a random term of @s@ nodes under @d@ binders.
gen :: Int -> Int -> Word64 -> (Raw, Word64)
gen d s g0
  | s <= 1 && d > 0 = (RVar (pick g d), g)
  | d == 0 || s == 2 || pick g 100 < 50 =
      let (body, g') = gen (d + 1) (s - 1) g in (RLam body, g')
  | otherwise =
      let k = 1 + pick (next g) (s - 2)
          (fun, g1) = gen d k (next (next g))
          (arg, g2) = gen d (s - 1 - k) g1
       in (RApp fun arg, g2)
  where
    g = next g0

toTerm :: Foil.Distinct n => Foil.Scope n -> [Foil.Name n] -> Raw -> Term n
toTerm _ names (RVar i) = Var (names !! i)
toTerm scope names (RApp fun arg) = Node (App (toTerm scope names fun) (toTerm scope names arg))
toTerm scope names (RLam body) = Foil.withFresh scope $ \binder ->
  let scope' = Foil.extendScope binder scope
   in Node (Lam (ScopedAST binder (toTerm scope' (Foil.nameOf binder : map Foil.sink names) body)))

closed :: Raw -> Term Foil.VoidS
closed = toTerm Foil.emptyScope []

-- | 100 terms of 4 to 32 nodes.
corpus :: [Raw]
corpus = go (100 :: Int) 42
  where
    go 0 _ = []
    go k g =
      let (t, g') = gen 0 (4 + pick g 29) (next g)
       in t : go (k - 1) g'

main :: IO ()
main = do
  terms <- evaluate (force (map closed corpus))
  big <- evaluate (force (closed (fst (gen 0 20000 7))))
  defaultMain
    [ bench "rnf, 100 small terms" $ nf (foldr (\t r -> rnf t `seq` r) ()) terms
    , bench "rnf, one term of 20000 nodes" $ nf rnf big
    ]
