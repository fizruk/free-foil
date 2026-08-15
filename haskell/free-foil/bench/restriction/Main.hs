{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Restriction benchmark: cutting a chain of binders down to the ones a term
-- actually uses, the two ways it can be done.
--
-- This is the operation a parametrised module performs when it discharges a
-- declaration over the parameters it uses, and it is where the library's
-- account of /restriction/ is put under pressure. The question is the same
-- either way — which of these binders can the term do without? — and there are
-- two answers:
--
-- * ask once. 'supportOf' computes the term's free names in one traversal, and
--   'Foil.withThinnedNameBinderList' cuts the chain down to that set in one
--   step, so the term is walked once whatever the number of binders;
--
-- * ask per binder. 'unsinkAST' answers for one binder at a time, and each call
--   recomputes the term's support, so the term is walked once per binder.
--
-- The second is the shorter thing to write, and it is what a language
-- implementation reaches for first. The benchmark is here to say what it costs:
-- the two should separate linearly in the number of binders, and the point at
-- which they do is worth knowing, since a module with three parameters is the
-- common case and one with fourteen is not unheard of.
--
-- Both directions report the same number, and the benchmark checks that they
-- agree before timing them, so a change that breaks one is not silently
-- measured against the other.
module Main (main) where

import           Data.Bifoldable         (Bifoldable (..))
import           Data.List               (foldl')
import           Data.List.NonEmpty      (NonEmpty (..), nonEmpty)
import           Test.Tasty.Bench

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil (AST (..), ScopedAST (..), pattern Var,
                                          supportOf, unsinkAST)

-- * A signature to build terms over

-- | Application and λ, which is all a term needs to have free variables and
-- binders in it.
data LamSig scope term
  = App term term
  | Lam scope
  deriving (Functor, Foldable, Traversable)

instance Bifoldable LamSig where
  bifoldMap f g = \case
    App l r -> g l <> g r
    Lam body -> f body

-- | Terms whose binders are single names, which is what a parameter block is.
type Term = AST Foil.NameBinder LamSig

-- * The workload

-- | A chain of @n@ binders over the empty scope.
--
-- The continuation is handed the innermost scope, the chain, and the scope
-- before each binder, innermost first.
withChain
  :: forall r. Int
  -> (forall l. Foil.Distinct l
        => Foil.NameBinderList Foil.VoidS l -> r)
  -> r
withChain total cont = go total Foil.emptyScope Foil.NameBinderListEmpty
  where
    go :: forall i. Foil.Distinct i
       => Int -> Foil.Scope i -> Foil.NameBinderList Foil.VoidS i -> r
    go 0 _scope chain = cont chain
    go k scope chain =
      Foil.withFresh scope $ \binder ->
        go (k - 1) (Foil.extendScope binder scope) (Foil.snocNameBinderList chain binder)

-- | A term over the given names, of a size the caller controls.
--
-- The names are used in a left-nested application spine, repeated until the
-- term has @uses@ leaves. Which names appear decides how far the chain can be
-- thinned; how many leaves there are decides what a traversal of the term
-- costs, and the two are what the benchmark varies.
spine :: Int -> NonEmpty (Foil.Name l) -> Term l
spine uses (first :| rest) = foldl' apply (Var first) (map Var more)
  where
    apply f x = Node (App f x)
    more = take (max 0 (uses - 1)) (cycle (first : rest))

-- * The two directions

-- | Ask once: one 'supportOf', then one thinning.
thinOnce :: Foil.Distinct l => Foil.NameBinderList Foil.VoidS l -> Term l -> Int
thinOnce chain term =
  Foil.withThinnedNameBinderList (supportOf term) chain $ \thinned ->
    length (Foil.namesOfPattern thinned)

-- | Ask per binder: peel the chain from the inside out, asking 'unsinkAST' at
-- each binder whether the term can do without it, and abstracting over it when
-- it cannot.
--
-- This is the shape the alternative really has, and the reason it costs what it
-- costs: the term is /rebuilt/ as the peeling goes, so each 'unsinkAST' faces a
-- different (and larger) term and has to compute its support afresh. Asking the
-- same question about one fixed term would let the compiler share that
-- computation, and then the two directions would be indistinguishable — which
-- is what a first version of this benchmark measured, and why it is written out
-- like this instead.
askPerBinder
  :: forall n l. Foil.Distinct n
  => Foil.Scope n -> Foil.NameBinderList n l -> Term l -> Int
askPerBinder scope binders term = fst (peel scope binders term)
  where
    peel :: forall m i. Foil.Distinct m
         => Foil.Scope m -> Foil.NameBinderList m i -> Term i -> (Int, Term m)
    peel _scope' Foil.NameBinderListEmpty inner = (0, inner)
    peel scope' (Foil.NameBinderListCons binder rest) inner =
      case (Foil.assertDistinct binder, Foil.assertExt binder) of
        (Foil.Distinct, Foil.Ext) ->
          let (kept, body) = peel (Foil.extendScope binder scope') rest inner
           in case unsinkAST scope' body of
                Just dropped -> (kept, dropped)
                Nothing      -> (kept + 1, Node (Lam (ScopedAST binder body)))

-- | Both directions, at one size, with the answers checked against each other.
--
-- @binders@ is how many the chain has, @keep@ how many of them the term names,
-- and @uses@ how many leaves the term has.
sizedBench :: Int -> Int -> Int -> Benchmark
sizedBench binders keep uses =
  withChain binders $ \chain ->
    case nonEmpty (take keep (Foil.namesOfPattern chain)) of
      Nothing -> error "a benchmark size must use at least one binder"
      Just names ->
        let term = spine uses names
            once = thinOnce chain term
            perBinder = askPerBinder Foil.emptyScope chain term
         in if once /= perBinder
              then error ("the two directions disagree: " <> show (once, perBinder))
              else bgroup (show binders <> " binders, " <> show keep <> " used, "
                            <> show uses <> " leaves")
                     [ bench "thin once"      (whnf (thinOnce chain) term)
                     , bench "ask per binder"
                         (whnf (askPerBinder Foil.emptyScope chain) term)
                     ]

main :: IO ()
main = defaultMain
  -- The term is held at one size while the chain grows, so what separates the
  -- two directions is the number of binders and nothing else.
  [ bgroup "a fixed term, a growing parameter block"
      [ sizedBench binders 2 64 | binders <- [1, 3, 7, 14, 32] ]
  -- And the other way round: a fixed block, a growing term.
  , bgroup "a fixed parameter block, a growing term"
      [ sizedBench 8 2 uses | uses <- [16, 64, 256, 1024] ]
  ]
