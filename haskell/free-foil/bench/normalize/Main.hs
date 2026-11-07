{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

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
--
-- The second group runs the same workload with binders that carry a payload,
-- the type of the bound name, as in @λ(s : A). λ(z : s). s (s z)@. The type
-- of @z@ mentions @s@, so every β-step substitutes into payloads too.
module Main (main) where

import           Test.Tasty.Bench

import           Control.Monad.Foil            (S (VoidS))
import qualified Control.Monad.Foil            as Foil
import           Control.Monad.Free.Foil       (AST, pattern Var, substitute)
import           Control.Monad.Free.Foil.Example (Expr, ExprF, churchN, nf', pattern AppE, pattern LamE)

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

-- * Binders with payloads

-- | A binder with the type of its name, in the scope before it.
data Typed (n :: Foil.S) (l :: Foil.S) where
  Typed :: TExpr n -> Foil.NameBinder n l -> Typed n l

-- | λ-terms whose binders carry types.
type TExpr = AST Typed ExprF

instance Foil.CoSinkable Typed where
  coSinkabilityProof rename (Typed ty x) cont =
    Foil.coSinkabilityProof rename x $ \rename' x' -> cont rename' (Typed (Foil.sinkabilityProof rename ty) x')

  withPattern withBinder _ _ scope (Typed ty x) cont =
    withBinder scope x $ \fx x' ->
      cont fx (Typed (Foil.transportPayload scope Foil.verbatimTransport ty) x') (Foil.extendScope x' scope)

  type Payload Typed = TExpr

  withMappedPattern refresh extend _ mapPayload scope m (Typed ty x) cont =
    refresh scope x $ \x' ->
      cont (extend m x x') (Typed (mapPayload scope m ty) x') (Foil.extendScope x' scope)

  foldMapPayloads f (Typed ty _) = f ty

instance Foil.SinkableK Typed where
  sinkabilityProofK = Foil.sinkabilityProofKViaCoSinkable

-- | The size of a term with its payloads.
sizeOfTyped :: TExpr n -> Int
sizeOfTyped = \case
  Var{}                 -> 1
  AppE f x              -> 1 + sizeOfTyped f + sizeOfTyped x
  LamE (Typed ty _) body -> 1 + sizeOfTyped ty + sizeOfTyped body

-- | Weak head normal form, as 'Control.Monad.Free.Foil.Example.whnf'.
whnfTyped :: Foil.Distinct n => Foil.Scope n -> TExpr n -> TExpr n
whnfTyped scope = \case
  AppE fun arg -> case whnfTyped scope fun of
    LamE (Typed _ x) body -> whnfTyped scope (substitute scope (Foil.addSubst Foil.identitySubst x arg) body)
    fun' -> AppE fun' arg
  t -> t

-- | Normal form, as 'Control.Monad.Free.Foil.Example.nf'. Payloads are
-- substituted into, not normalised.
nfTyped :: Foil.Distinct n => Foil.Scope n -> TExpr n -> TExpr n
nfTyped scope = \case
  LamE binder@(Typed _ x) body -> case Foil.assertDistinct x of
    Foil.Distinct -> LamE binder (nfTyped (Foil.extendScope x scope) body)
  AppE fun arg -> case whnfTyped scope fun of
    LamE (Typed _ x) body -> nfTyped scope (substitute scope (Foil.addSubst Foil.identitySubst x arg) body)
    fun' -> AppE (nfTyped scope fun') (nfTyped scope arg)
  t -> t

-- | The Church numeral @n@ with typed binders: @λ(s : A). λ(z : s). s (… (s z))@.
churchTyped :: Foil.Distinct n => Foil.Scope n -> Foil.Name n -> Int -> TExpr n
churchTyped scope a n = Foil.withFresh scope $ \s ->
  Foil.withFresh (Foil.extendScope s scope) $ \z ->
    LamE (Typed (Var a) s) $
      LamE (Typed (Var (Foil.nameOf s)) z) $
        iterate (AppE (Var (Foil.sink (Foil.nameOf s)))) (Var (Foil.nameOf z)) !! n

-- | @m@ to the @n@ with typed binders, normalised and walked, in the scope of
-- the one free name @A@.
normalizedTyped :: Int -> Int -> Int
normalizedTyped n m = Foil.withFresh Foil.emptyScope $ \a ->
  let scope = Foil.extendScope a Foil.emptyScope
      term = AppE (churchTyped scope (Foil.nameOf a) n) (churchTyped scope (Foil.nameOf a) m)
  in sizeOfTyped (nfTyped scope term)

main :: IO ()
main = defaultMain
  [ bgroup "nf of Church m^n"
      [ bench "8^2  = 64"   $ whnf normalized (power 2 8)
      , bench "4^3  = 64"   $ whnf normalized (power 3 4)
      , bench "12^2 = 144"  $ whnf normalized (power 2 12)
      , bench "2^8  = 256"  $ whnf normalized (power 8 2)
      , bench "2^10 = 1024" $ whnf normalized (power 10 2)
      ]
  , bgroup "nf of typed Church m^n"
      [ bench "8^2  = 64"   $ whnf (uncurry normalizedTyped) (2, 8)
      , bench "2^8  = 256"  $ whnf (uncurry normalizedTyped) (8, 2)
      , bench "2^10 = 1024" $ whnf (uncurry normalizedTyped) (10, 2)
      ]
  ]
