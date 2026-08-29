{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | A bidirectional type checker for MLTT.
--
-- The interesting part is not the typing rules, which are standard, but how
-- little scope handling they need: the foil's 'Foil.withFresh' allocates the
-- variable, 'Foil.NameMap' holds the context, and 'instantiate' opens a binder.
-- Nothing here manipulates a de Bruijn index or a name supply by hand.
--
-- One rule is worth reading for the design: to check @λ p ⇒ e@ against
-- @Π (q : A) → B@, 'check' allocates /one/ fresh variable and opens both @p@
-- and @q@ at it. The two patterns need not have the same shape, and neither
-- needs to bind anything, so @λ (x, y) ⇒ e@ against @Π (z : Σ …) → B@ and
-- @λ _ ⇒ e@ against @Π (z : A) → B@ are both handled by the same rule.
--
-- == What this checker deliberately does not do
--
-- It is a demonstration of scope handling, not a type checker anyone should
-- copy wholesale. Four omissions are worth naming, because each is somebody
-- else's work in this ecosystem rather than a gap to be filled here.
--
-- * __No elaboration.__ 'infer' returns a type and discards everything else,
--   so there is no elaborated output term, no implicit arguments, and no
--   inserted coercions. The library does have a scope-indexed annotation layer
--   ("Control.Monad.Free.Foil.Annotated"); it is not used here.
-- * __No normalisation by evaluation.__ Conversion normalises both sides and
--   compares them ('Language.MLTT.Eval.conv'). There are no closures, no
--   delayed substitutions, and no readback.
-- * __No generic typing algebra.__ The rules below are written by hand for
--   this one signature. Deriving a checker from per-constructor typing rules,
--   and the Pfenning recipe that chooses the judgement, are a separate line of
--   work.
-- * __No metavariables.__ No holes, no unification, no higher-order matching.
--   Generic second-order matching, higher-order preunification, and pattern
--   unification over free foil are Kudasov, Starikov, Ivanov, and Afliatonov's,
--   UNIF 2025 (<https://hal.science/hal-05148806 HAL record>), implemented in
--   <https://github.com/fedor-ivn/free-foil-hou free-foil-hou>.
--
-- It is also inconsistent on purpose: see 'Language.MLTT.Eval.nf'.
module Language.MLTT.Typecheck where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil
import           Data.ZipMatchK               (ZipMatchK)
import           Language.MLTT.Eval
import           Language.MLTT.Impl.Generated

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Language.MLTT.Impl.Generated
-- >>> import Language.MLTT.Eval

-- * Contexts

-- | Everything the type checker knows about the names in scope @n@: the scope
-- itself, a /total/ map giving each name its type, and a /total/ map saying
-- what each name unfolds to.
data Ctx a n = Ctx
  { ctxScope :: Foil.Scope n
  , ctxTypes :: Foil.NameMap n (Term' a n)
  , ctxDefs  :: Defs a n
  }

-- | The empty context.
emptyCtx :: Ctx a Foil.VoidS
emptyCtx = Ctx Foil.emptyScope Foil.emptyNameMap emptyDefs

-- | Extend a context with a fresh variable of a given type.
withVar
  :: Foil.Distinct n
  => Ctx a n
  -> Term' a n            -- ^ The type of the new variable.
  -> (forall l. Foil.DExt n l => Ctx a l -> Foil.Name l -> r)
  -> r
-- The variable is ephemeral, existing only while the checker is under the
-- binder, so it is allocated with no reservation. Its raw name may land
-- inside some module's stripe. That is harmless, because it never enters a
-- module's scope and nothing about linking rests on term-internal names.
withVar ctx ty cont = withVarBinder Foil.fullNameRange ctx ty $ \ctx' binder ->
  cont ctx' (Foil.nameOf binder)

-- | Extend a context with a fresh variable, handing back its /binder/.
--
-- A caller that intends to abstract over the variable again later needs the
-- binder and not just the name, since a binder is what a @Π@ or a @λ@ is built
-- from. See "Language.MLTT.Telescope".
withVarBinder
  :: Foil.Distinct n
  => Foil.NameRange       -- ^ The reservation to allocate the name from.
  -> Ctx a n
  -> Term' a n            -- ^ The type of the new variable.
  -> (forall l. Foil.DExt n l => Ctx a l -> Foil.NameBinder n l -> r)
  -> r
withVarBinder range ctx ty cont = Foil.withFreshIn range (ctxScope ctx) $ \binder ->
  cont (extend ctx binder ty Nothing) binder

-- | Add one binder to a context. Sinking the two maps is \(O(1)\); only the
-- new entry is inserted.
--
-- A top-level definition goes through this too, with a 'Just' value: it is
-- an ordinary name in scope whose 'Def' is not 'Nothing', so
-- \(\delta\)-reduction unfolds it and nothing else has to change. That makes
-- a top-level constant a 'Foil.Name' in a growing scope, which is one of the
-- two possible designs for a global environment.
extend
  :: Foil.DExt n l
  => Ctx a n -> Foil.NameBinder n l -> Term' a n -> Maybe (Term' a n) -> Ctx a l
extend ctx binder ty value = Ctx
  { ctxScope = Foil.extendScope binder (ctxScope ctx)
  , ctxTypes = Foil.addNameBinder binder (Foil.sink ty) (Foil.sink1 (ctxTypes ctx))
  , ctxDefs  = Foil.addNameBinder binder (Def (Foil.sink1 value)) (Foil.sink1 (ctxDefs ctx))
  }

-- | Reduce a term to weak head normal form in a context.
whnfIn :: Foil.Distinct n => Ctx a n -> Term' a n -> Term' a n
whnfIn ctx = whnf (ctxScope ctx) (ctxDefs ctx)

-- * Type checking

-- | What the type checker reports. Terms are shown in the raw syntax, so an
-- error message reads like the source it came from.
type TypeError = String

-- | Infer the type of a term.
--
-- >>> infer emptyCtx (desugar ("(λ x ⇒ x : 𝟙 → 𝟙) tt" :: Term Foil.VoidS))
-- Right 𝟙
--
-- The second component of a pair is typed by substituting the first into the
-- Σ-type's codomain, so a projection is dependent even when the pair is not:
--
-- >>> infer emptyCtx (desugar ("π₂ (𝟙, tt)" :: Term Foil.VoidS))
-- Right 𝟙
infer
  :: forall a n. (Foil.Distinct n, ZipMatchK a)
  => Ctx a n -> Term' a n -> Either TypeError (Term' a n)
infer ctx = \case
  Var x -> return (Foil.lookupName x (ctxTypes ctx))

  Universe loc -> return (Universe loc)   -- type-in-type, deliberately
  UnitType loc -> return (Universe loc)
  UnitVal loc  -> return (UnitType loc)

  Pi loc ty pat body -> do
    check ctx ty (Universe loc)
    withVar ctx ty $ \ctx' x ->
      check ctx' (instantiate (ctxScope ctx') pat (Var x) body) (Universe loc)
    return (Universe loc)

  Sigma loc ty pat body -> do
    check ctx ty (Universe loc)
    withVar ctx ty $ \ctx' x ->
      check ctx' (instantiate (ctxScope ctx') pat (Var x) body) (Universe loc)
    return (Universe loc)

  -- @A → B@ and @A × B@ are sugar; see 'desugar'. They are handled here too so
  -- that the checker is total on unsugared input.
  Arrow loc t1 t2   -> infer ctx (Pi loc t1 (PatternWildcard loc) t2)
  Product loc t1 t2 -> infer ctx (Sigma loc t1 (PatternWildcard loc) t2)

  App loc f x -> do
    tf <- infer ctx f
    case whnfIn ctx tf of
      Pi _loc tyA pat tyB -> do
        check ctx x tyA
        return (instantiate (ctxScope ctx) pat x tyB)
      tf' -> Left (expected "a Π-type" tf' (App loc f x))

  First loc t -> do
    tt <- infer ctx t
    case whnfIn ctx tt of
      Sigma _loc tyA _pat _tyB -> return tyA
      tt'                      -> Left (expected "a Σ-type" tt' (First loc t))

  Second loc t -> do
    tt <- infer ctx t
    case whnfIn ctx tt of
      Sigma _loc _tyA pat tyB -> return (instantiate (ctxScope ctx) pat (First loc t) tyB)
      tt'                     -> Left (expected "a Σ-type" tt' (Second loc t))

  -- A pair is inferable only non-dependently; a dependent pair has to be
  -- checked against its Σ-type.
  Pair loc l r -> do
    tl <- infer ctx l
    tr <- infer ctx r
    return (Sigma loc tl (PatternWildcard loc) tr)

  Ann loc t ty -> do
    check ctx ty (Universe loc)
    check ctx t ty
    return ty

  Let _loc value pat body -> do
    _ <- infer ctx value
    infer ctx (instantiate (ctxScope ctx) pat value body)

  IdType loc tyA x y -> do
    check ctx tyA (Universe loc)
    check ctx x tyA
    check ctx y tyA
    return (Universe loc)

  Refl loc x -> do
    tx <- infer ctx x
    return (IdType loc tx x x)

  J loc motive base path -> do
    tp <- infer ctx path
    case whnfIn ctx tp of
      IdType _loc tyA a b -> do
        check ctx motive (motiveType (ctxScope ctx) loc tyA a)
        check ctx base (App loc (App loc motive a) (Refl loc a))
        return (App loc (App loc motive b) path)
      tp' -> Left (expected "an identity type" tp' path)

  term@(Lam _loc _pat _body) ->
    Left ("cannot infer a type for a λ-abstraction; add an ascription: " <> show term)

-- | The type of the motive of @J@: @Π (x : A) → Id(A, a, x) → 𝕌@.
motiveType
  :: Foil.Distinct n
  => Foil.Scope n -> a -> Term' a n -> Term' a n -> Term' a n
motiveType scope loc tyA a = Foil.withFresh scope $ \binder ->
  Pi loc tyA (PatternVar loc binder)
    (Pi loc (IdType loc (Foil.sink tyA) (Foil.sink a) (Var (Foil.nameOf binder)))
            (PatternWildcard loc)
            (Universe loc))

-- | Check a term against a type.
--
-- >>> check emptyCtx (desugar ("λ A ⇒ λ x ⇒ x" :: Term Foil.VoidS)) (desugar "Π (A : 𝕌) → Π (x : A) → A")
-- Right ()
--
-- Pattern binders are checked against the type of what they destructure:
--
-- >>> check emptyCtx (desugar ("λ (A, x) ⇒ x" :: Term Foil.VoidS)) (desugar "Π (p : Σ (A : 𝕌) × A) → π₁ p")
-- Right ()
check
  :: forall a n. (Foil.Distinct n, ZipMatchK a)
  => Ctx a n -> Term' a n -> Term' a n -> Either TypeError ()
check ctx term ty = case (term, whnfIn ctx ty) of
  (Lam _loc pat body, Pi _loc' tyA patA tyB) ->
    withVar ctx tyA $ \ctx' x ->
      check ctx'
        (instantiate (ctxScope ctx') pat  (Var x) body)
        (instantiate (ctxScope ctx') patA (Var x) tyB)

  (Lam _loc _pat _body, ty') ->
    Left ("a λ-abstraction cannot have type " <> show ty')

  (Pair _loc l r, Sigma _loc' tyA patA tyB) -> do
    check ctx l tyA
    check ctx r (instantiate (ctxScope ctx) patA l tyB)

  _ -> do
    ty' <- infer ctx term
    if conv (ctxScope ctx) (ctxDefs ctx) ty ty'
      then return ()
      else Left (unlines
        [ "expected type: " <> show ty
        , "  actual type: " <> show ty'
        , "     for term: " <> show term ])

-- * Helpers

-- | A uniform "expected X, got Y" message.
expected :: String -> Term' a n -> Term' a n -> TypeError
expected what ty term = unlines
  [ "expected " <> what <> ", but the type is: " <> show ty
  , "  for term: " <> show term ]
