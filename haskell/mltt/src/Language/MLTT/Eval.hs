{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Evaluation and conversion for MLTT.
--
-- Reduction is deliberately naive: weak head normal forms computed by
-- 'whnf', full normal forms by 'nf', and conversion by \(\alpha\)-equivalence
-- of normal forms ('conv'). The library supplies substitution and
-- \(\alpha\)-equivalence, so what is written here is only the reduction rules
-- themselves.
module Language.MLTT.Eval where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor              (bimap)
import           Data.ZipMatchK              (ZipMatchK)
import           Language.MLTT.Impl.Generated

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Language.MLTT.Impl.Generated
-- >>> import qualified Language.MLTT.Syntax.Abs as Raw

-- * Desugaring

-- | Replace the non-dependent @A → B@ and @A × B@ by @Π (_ : A) → B@ and
-- @Σ (_ : A) × B@.
--
-- Both are genuinely sugar: a wildcard pattern binds nothing, so the codomain
-- cannot depend on the domain. Doing this once, right after parsing, keeps the
-- evaluator and the type checker down to one rule per former.
--
-- >>> desugar ("𝟙 → 𝟙" :: Term Foil.VoidS)
-- Π (_ : 𝟙) → 𝟙
desugar :: Term' a n -> Term' a n
desugar = \case
  Var x                       -> Var x
  Node (ArrowSig loc t1 t2)   -> Pi loc (desugar t1) (PatternWildcard loc) (desugar t2)
  Node (ProductSig loc t1 t2) -> Sigma loc (desugar t1) (PatternWildcard loc) (desugar t2)
  Node node                   -> Node (bimap desugarScoped desugar node)
  where
    desugarScoped (ScopedAST binder body) = ScopedAST binder (desugar body)

-- * Matching patterns

-- | The substitution that matches a pattern against a term.
--
-- Each variable the pattern binds is sent to the corresponding projection of
-- the term, so that a pair pattern is eliminated by @π₁@ and @π₂@ rather than
-- by a separate matching judgement. This is the one place where the shape of a
-- custom pattern matters to the semantics.
matchPattern
  :: forall a n l o. Foil.DExt n o
  => Pattern' a n l   -- ^ Pattern extending scope @n@.
  -> Term' a o        -- ^ The term it is matched against, in a larger scope @o@.
  -> Foil.Substitution (Term' a) l o
matchPattern pat0 term0 = go pat0 term0 (Foil.sink (Foil.identitySubst :: Foil.Substitution (Term' a) n n))
  where
    go :: Pattern' a i l' -> Term' a o -> Foil.Substitution (Term' a) i o -> Foil.Substitution (Term' a) l' o
    go (PatternWildcard _loc)  _ = id
    go (PatternVar _loc x)     e = \subst -> Foil.addSubst subst x e
    go (PatternPair loc l r)   e = go r (Second loc e) . go l (First loc e)

-- | Instantiate the body of a binder: substitute a term for the pattern it was
-- bound by. This is the workhorse of \(\beta\), of @let@, and of every rule in
-- the type checker that has to look underneath a binder.
--
-- The target scope @o@ may be larger than the pattern's own scope @n@, which is
-- what lets the type checker open a \(\lambda\) and the \(\Pi\)-type it is
-- checked against at one and the same fresh variable.
instantiate
  :: Foil.DExt n o
  => Foil.Scope o
  -> Pattern' a n l
  -> Term' a o      -- ^ The term the pattern is matched against.
  -> Term' a l      -- ^ The body, under the pattern.
  -> Term' a o
instantiate scope pat term body = substitute scope (matchPattern pat term) body

-- * Definitions

-- | What a name in scope may unfold to: 'Nothing' for a local variable,
-- 'Just' for a top-level definition that \(\delta\)-reduction unfolds.
--
-- This is a @newtype@ rather than a bare 'Maybe' so that it is 'Foil.Sinkable',
-- which is what lets 'extendDefs' enter a binder in \(O(1)\).
newtype Def a n = Def { getDef :: Maybe (Term' a n) }

instance Foil.Sinkable (Def a) where
  sinkabilityProof rename (Def value) =
    Def (fmap (Foil.sinkabilityProof rename) value)

-- | A /total/ map from the names in scope to what they unfold to.
type Defs a n = Foil.NameMap n (Def a n)

-- | No definitions in the empty scope.
emptyDefs :: Defs a Foil.VoidS
emptyDefs = Foil.emptyNameMap

-- | Enter a pattern: every name it binds is a local variable, so unfolds to
-- nothing.
extendDefs
  :: (Foil.CoSinkable binder, Foil.DExt n l)
  => binder n l -> Defs a n -> Defs a l
extendDefs binder defs =
  Foil.addNameBinders binder (repeat (Def Nothing)) (Foil.sinkContainer defs)

-- * Reduction

-- | Compute the weak head normal form of a term.
--
-- >>> let scope = Foil.emptyScope
-- >>> whnf scope emptyDefs (desugar ("(λ (x, y) → y) (tt, λ z → z)" :: Term Foil.VoidS))
-- λ x0 → x0
--
-- Projections reduce on an explicit pair, and @J@ on @refl@:
--
-- >>> whnf scope emptyDefs (desugar ("π₁ (tt, 𝕌)" :: Term Foil.VoidS))
-- tt
-- >>> whnf scope emptyDefs (desugar ("J (λ x → λ p → 𝟙, tt, refl (tt))" :: Term Foil.VoidS))
-- tt
whnf :: forall a n. Foil.Distinct n => Foil.Scope n -> Defs a n -> Term' a n -> Term' a n
whnf scope defs = go
  where
    go :: Term' a n -> Term' a n
    go = \case
      Var x -> case getDef (Foil.lookupName x defs) of
        Just value -> go value
        Nothing    -> Var x
      App loc f x -> case go f of
        Lam _loc binder body -> go (instantiate scope binder x body)
        f'                   -> App loc f' x
      First loc t -> case go t of
        Pair _loc l _r -> go l
        t'             -> First loc t'
      Second loc t -> case go t of
        Pair _loc _l r -> go r
        t'             -> Second loc t'
      J loc motive base path -> case go path of
        Refl _loc _x -> go base
        path'        -> J loc motive base path'
      Let _loc value binder body -> go (instantiate scope binder value body)
      Ann _loc t _ty -> go t
      t -> t

-- | Compute the full normal form of a term, reducing under binders.
--
-- Note that MLTT here has type-in-type, so this can diverge on a well-typed
-- term. That is a deliberate simplification: the demo is about scoping, not
-- about consistency.
--
-- >>> nf Foil.emptyScope emptyDefs (desugar ("λ f → λ x → (λ y → f y) x" :: Term Foil.VoidS))
-- λ x0 → λ x1 → x0 x1
nf :: forall a n. Foil.Distinct n => Foil.Scope n -> Defs a n -> Term' a n -> Term' a n
nf scope defs term = case whnf scope defs term of
    Var x     -> Var x
    Node node -> Node (bimap nfScoped (nf scope defs) node)
  where
    nfScoped :: ScopedTerm' a n -> ScopedTerm' a n
    nfScoped (ScopedAST binder body) =
      case (Foil.assertExt binder, Foil.assertDistinct binder) of
        (Foil.Ext, Foil.Distinct) -> ScopedAST binder
          (nf (Foil.extendScopePattern binder scope) (extendDefs binder defs) body)

-- | Conversion: are two terms equal up to reduction and renaming of bound
-- variables?
--
-- >>> conv Foil.emptyScope emptyDefs (desugar ("(λ x → x) tt" :: Term Foil.VoidS)) (desugar "tt")
-- True
-- >>> conv Foil.emptyScope emptyDefs (desugar ("λ x → x" :: Term Foil.VoidS)) (desugar "λ y → tt")
-- False
conv
  :: (Foil.Distinct n, ZipMatchK a)
  => Foil.Scope n -> Defs a n -> Term' a n -> Term' a n -> Bool
conv scope defs l r = alphaEquiv scope (nf scope defs l) (nf scope defs r)
