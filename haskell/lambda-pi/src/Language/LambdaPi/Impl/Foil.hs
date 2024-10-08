{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Foil implementation of the \(\lambda\Pi\)-calculus (with pairs).
--
-- The following is implemented __manually__ in this module:
--
-- 1. Scope-safe AST for \(\lambda\Pi\)-terms.
-- 2. Correct capture-avoiding substitution (see 'substitute').
-- 3. Conversion between scope-safe and raw term representation (the latter is generated via BNFC), see 'toFoilTerm' and 'fromFoilTerm'.
-- 4. Helper functions for patterns. See 'extendScopePattern' and 'withRefreshedPattern'.
-- 5. \(\alpha\)-equivalence checks ('alphaEquiv' and 'alphaEquivRefreshed') and \(\alpha\)-normalization helpers ('refreshExpr').
-- 6. Computation of weak head normal form (WHNF) and normal form (NF), see 'whnf' and 'nf'.
-- 7. Entry point, gluing everything together. See 'defaultMain'.
--
-- This implementation supports (nested) patterns for pairs.
--
-- This is a baseline implementation, see other examples for partial automation:
--
-- 1. "Language.LambdaPi.Impl.FreeFoil" allows to reuse generalized substitution and \(\alpha\)-equivalence (and, in theory, more complicated algorithms).
-- 2. "Language.LambdaPi.Impl.FoilTH" works well with patterns and generates conversion functions and helpers for patterns.
-- 3. "Language.LambdaPi.Impl.FreeFoilTH" combines the benefits of the above, when it is possible to generate the signature automatically.
module Language.LambdaPi.Impl.Foil where

import           Control.Monad.Foil
import           Control.Monad.Foil.Relative
import           Data.Coerce                     (coerce)
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.String
import qualified Language.LambdaPi.Syntax.Abs    as Raw
import           Language.LambdaPi.Syntax.Layout (resolveLayout)
import           Language.LambdaPi.Syntax.Lex    (tokens)
import           Language.LambdaPi.Syntax.Par    (pProgram, pTerm)
import           Language.LambdaPi.Syntax.Print  (printTree)
import           System.Exit                     (exitFailure)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import Control.Monad.Foil

-- * Scope-safe AST

-- | Type of scope-safe \(\lambda\Pi\)-terms with pairs.
data Expr n where
  -- | Variables: \(x\)
  VarE  :: Name n -> Expr n

  -- | Application: \((t_1 \; t_2)\)
  AppE  :: Expr n -> Expr n -> Expr n
  -- | Abstraction (with patterns): \(\lambda p. t\)
  LamE  :: Pattern n l -> Expr l -> Expr n
  -- | \(\prod\)-types (with patterns): \(\prod_{p : T_1} T_2\)
  PiE   :: Pattern n l -> Expr n -> Expr l -> Expr n

  -- | Pair of terms: \(\langle t_1, t_2 \rangle\)
  PairE :: Expr n -> Expr n -> Expr n
  -- | First projection: \(\pi_1(t)\)
  FirstE :: Expr n -> Expr n
  -- | Second projection: \(\pi_2(t)\)
  SecondE :: Expr n -> Expr n
  -- | Product type (non-dependent): \(T_1 \times T_2\)
  ProductE :: Expr n -> Expr n -> Expr n

  -- | Universe (type of types): \(\mathcal{U}\)
  UniverseE :: Expr n

instance Show (Expr VoidS) where
  show = printTree . fromFoilTerm'

instance IsString (Expr VoidS) where
  fromString input =
    case pTerm (tokens input) of
      Left err -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
      Right term -> toFoilTermClosed term

-- | Patterns.
data Pattern n l where
  -- | Wildcard pattern: \(_\)
  PatternWildcard :: Pattern n n
  -- | Variable pattern: \(x\)
  PatternVar :: NameBinder n l -> Pattern n l
  -- | Pair pattern: \((p_1, p_2)\)
  PatternPair :: Pattern n i -> Pattern i l -> Pattern n l

instance CoSinkable Pattern where
  coSinkabilityProof rename pattern cont =
    case pattern of
      PatternWildcard ->
        cont rename PatternWildcard
      PatternVar x ->
        coSinkabilityProof rename x $ \rename' x' ->
          cont rename' (PatternVar x')
      PatternPair l r ->
        coSinkabilityProof rename l $ \rename' l' ->
          coSinkabilityProof rename' r $ \rename'' r' ->
            cont rename'' (PatternPair l' r')

  withPattern withNameBinder id' combine scope pattern cont =
    case pattern of
      PatternWildcard -> cont id' PatternWildcard
      PatternVar x    -> withNameBinder scope x $ \f x' ->
        cont f (PatternVar x')
      PatternPair l r -> withPattern withNameBinder id' combine scope l $ \fl l' ->
        let scope' = extendScopePattern l' scope
        in withPattern withNameBinder id' combine scope' r $ \fr r' ->
              cont (combine fl fr) (PatternPair l' r')

instance UnifiablePattern Pattern where
  unifyPatterns PatternWildcard PatternWildcard = SameNameBinders emptyNameBinders
  unifyPatterns (PatternVar x) (PatternVar x') = unifyNameBinders x x'
  unifyPatterns (PatternPair l r) (PatternPair l' r') = case (assertDistinct l, assertDistinct l') of
    (Distinct, Distinct) -> unifyPatterns l l' `andThenUnifyPatterns` (r, r')
  unifyPatterns _ _ = NotUnifiable

instance InjectName Expr where
  injectName = VarE

instance RelMonad Name Expr where
  rreturn = VarE
  rbind scope e subst = case e of
    VarE name -> subst name
    AppE f x -> AppE (rbind scope f subst) (rbind scope x subst)
    LamE pattern body -> withRefreshedPattern' scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          body' = rbind scope' body subst'
      in LamE pattern' body'
    PiE pattern a b -> withRefreshedPattern' scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          a' = rbind scope a subst
          b' = rbind scope' b subst'
       in PiE pattern' a' b'
    PairE l r -> PairE (rbind scope l subst) (rbind scope r subst)
    FirstE t -> FirstE (rbind scope t subst)
    SecondE t -> SecondE (rbind scope t subst)
    ProductE l r -> ProductE (rbind scope l subst) (rbind scope r subst)
    UniverseE -> UniverseE

-- * Pretty-printing

-- | Default way to print a name using its internal 'Id'.
ppName :: Name n -> String
ppName name = "x" <> show (nameId name)

-- | Pretty-print a \(\lambda\Pi\)-term directly (without converting to raw term).
--
-- >>> ppExpr identity
-- "\955x0. x0"
-- >>> ppExpr (churchN 2)
-- "\955x0. \955x1. x0 (x0 (x1))"
ppExpr :: Expr n -> String
ppExpr = \case
  VarE name     -> ppName name
  AppE e1 e2    -> ppExpr e1 ++ " (" ++ ppExpr e2 ++ ")"
  LamE pat body -> "λ" ++ ppPattern pat ++ ". " ++ ppExpr body
  PiE pat a b -> "Π" ++ "(" ++ ppPattern pat ++ " : " ++ ppExpr a ++ "), " ++ ppExpr b
  PairE l r -> "(" ++ ppExpr l ++ "," ++ ppExpr r ++ ")"
  FirstE t -> "π₁(" ++ ppExpr t ++ ")"
  SecondE t -> "π₂(" ++ ppExpr t ++ ")"
  ProductE l r -> "(" ++ ppExpr l ++ " × " ++ ppExpr r ++ ")"
  UniverseE -> "𝕌"

-- | Pretty-print a pattern in a \(\lambda\Pi\)-term (without converting to raw pattern)..
ppPattern :: Pattern n l -> String
ppPattern = \case
  PatternWildcard -> "_"
  PatternVar x -> ppName (nameOf x)
  PatternPair l r -> "(" <> ppPattern l <> "," <> ppPattern r <> ")"

-- | Pretty-print a /closed/ scode-safe \(\lambda\Pi\)-term
-- using BNFC-generated printer (via 'Raw.Term').
printExpr :: Expr VoidS -> String
printExpr = printTree . fromFoilTermClosed
  [ Raw.VarIdent ("x" <> show i) | i <- [1 :: Integer ..] ]

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE pat body) = extendRenaming rename pat $ \rename' pat' ->
    LamE pat' (sinkabilityProof rename' body)
  sinkabilityProof rename (PiE pat a b) =
    extendRenaming rename pat $ \rename' pat' ->
      PiE pat' (sinkabilityProof rename a) (sinkabilityProof rename' b)
  sinkabilityProof rename (PairE l r) = PairE (sinkabilityProof rename l) (sinkabilityProof rename r)
  sinkabilityProof rename (FirstE t) = FirstE (sinkabilityProof rename t)
  sinkabilityProof rename (SecondE t) = SecondE (sinkabilityProof rename t)
  sinkabilityProof rename (ProductE l r) = ProductE (sinkabilityProof rename l) (sinkabilityProof rename r)
  sinkabilityProof _ UniverseE = UniverseE

-- * Substitution

-- | Perform substitution in a \(\lambda\Pi\)-term.
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE pattern body -> withRefreshedPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          body' = substitute scope' subst' body
       in LamE pattern' body'
    PiE pattern a b -> withRefreshedPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          a' = substitute scope subst a
          b' = substitute scope' subst' b
       in PiE pattern' a' b'
    PairE l r -> PairE (substitute scope subst l) (substitute scope subst r)
    FirstE t -> FirstE (substitute scope subst t)
    SecondE t -> SecondE (substitute scope subst t)
    ProductE l r -> ProductE (substitute scope subst l) (substitute scope subst r)
    UniverseE -> UniverseE

-- | Perform substitution in a \(\lambda\Pi\)-term
-- and normalize binders in the process.
substituteRefresh :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substituteRefresh scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substituteRefresh scope subst f) (substituteRefresh scope subst x)
    LamE pattern body -> withFreshPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          body' = substituteRefresh scope' subst' body
       in LamE pattern' body'
    PiE pattern a b -> withFreshPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          a' = substituteRefresh scope subst a
          b' = substituteRefresh scope' subst' b
       in PiE pattern' a' b'
    PairE l r -> PairE (substituteRefresh scope subst l) (substituteRefresh scope subst r)
    FirstE t -> FirstE (substituteRefresh scope subst t)
    SecondE t -> SecondE (substituteRefresh scope subst t)
    ProductE l r -> ProductE (substituteRefresh scope subst l) (substituteRefresh scope subst r)
    UniverseE -> UniverseE

-- * Conversion

-- ** From raw to foil

-- | Convert a raw pattern into a scope-safe one.
toFoilPattern
  :: Distinct n
  => Scope n                    -- ^ Outer scope (outside of pattern binding).
  -> Map Raw.VarIdent (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> Raw.Pattern                -- ^ Raw pattern.
  -> (forall l. DExt n l => Pattern n l -> Map Raw.VarIdent (Name l) -> r)
  -- ^ A continuation, accepting a scope-safe pattern and an updated variable mapping.
  -> r
toFoilPattern scope env pattern cont =
  case pattern of
    Raw.PatternWildcard _loc -> cont PatternWildcard env
    Raw.PatternVar _loc x -> withFresh scope $ \binder ->
      cont (PatternVar binder) (Map.insert x (nameOf binder) (sink <$> env))
    Raw.PatternPair _loc l r ->
      toFoilPattern scope env l $ \l' env' ->
        let scope' = extendScopePattern l' scope
         in toFoilPattern scope' env' r $ \r' env'' ->
              cont (PatternPair l' r') env''

-- | Convert a raw term into a scope-safe \(\lambda\Pi\)-term.
toFoilTerm
  :: Distinct n
  => Scope n                    -- ^ Target scope.
  -> Map Raw.VarIdent (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> Raw.Term                   -- ^ A raw term.
  -> Expr n
toFoilTerm scope env = \case
  Raw.Var _loc x ->
    case Map.lookup x env of
      Just name -> VarE name
      Nothing   -> error $ "unknown free variable: " <> show x

  Raw.App _loc t1 t2 ->
    AppE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  Raw.Lam _loc pattern (Raw.AScopedTerm _loc' body) ->
    toFoilPattern scope env pattern $ \pattern' env' ->
      let scope' = extendScopePattern pattern' scope
       in LamE pattern' (toFoilTerm scope' env' body)

  Raw.Pi _loc pattern a (Raw.AScopedTerm _loc' b) ->
    toFoilPattern scope env pattern $ \pattern' env' ->
      let scope' = extendScopePattern pattern' scope
       in PiE pattern' (toFoilTerm scope env a) (toFoilTerm scope' env' b)

  Raw.Pair _loc t1 t2 ->
    PairE (toFoilTerm scope env t1) (toFoilTerm scope env t2)
  Raw.First _loc t ->
    FirstE (toFoilTerm scope env t)
  Raw.Second _loc t ->
    SecondE (toFoilTerm scope env t)

  Raw.Product _loc t1 t2 ->
    ProductE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  Raw.Universe _loc -> UniverseE

-- | Convert a raw term into a closed scope-safe term.
toFoilTermClosed :: Raw.Term -> Expr VoidS
toFoilTermClosed = toFoilTerm emptyScope Map.empty

-- ** From foil to raw

-- | Convert a scope-safe pattern into a raw pattern.
fromFoilPattern
  :: [Raw.VarIdent]         -- ^ A stream of fresh variable identifiers.
  -> NameMap n Raw.VarIdent -- ^ A /total/ mapping for names in scope @n@.
  -> Pattern n l            -- ^ A scope-safe pattern that extends scope @n@ into scope @l@.
  -> ([Raw.VarIdent] -> NameMap l Raw.VarIdent -> Raw.Pattern -> r)
    -- ^ A continutation, accepting (smaller) stream of fresh variable identifiers, a mapping for the inner scope, and a raw pattern.
  -> r
fromFoilPattern freshVars env pattern cont =
  case pattern of
    PatternWildcard -> cont freshVars env (Raw.PatternWildcard loc)
    PatternVar z ->
      case freshVars of
        []   -> error "not enough fresh variables!"
        x:xs -> cont xs (addNameBinder z x env) (Raw.PatternVar loc x)
    PatternPair l r ->
      fromFoilPattern freshVars env l $ \freshVars' env' l' ->
        fromFoilPattern freshVars' env' r $ \freshVars'' env'' r' ->
          cont freshVars'' env'' (Raw.PatternPair loc l' r')
    where
      loc = error "location information is lost when converting from AST"

-- | Convert a scope-safe term into a raw term.
fromFoilTerm
  :: [Raw.VarIdent]         -- ^ A stream of fresh variable identifiers.
  -> NameMap n Raw.VarIdent -- ^ A /total/ mapping for names in scope @n@.
  -> Expr n                 -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTerm freshVars env = \case
  VarE name -> Raw.Var loc (lookupName name env)
  AppE t1 t2 -> Raw.App loc (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  LamE pattern body ->
    fromFoilPattern freshVars env pattern $ \freshVars' env' pattern' ->
      Raw.Lam loc pattern' (Raw.AScopedTerm loc (fromFoilTerm freshVars' env' body))
  PiE pattern a b ->
    fromFoilPattern freshVars env pattern $ \freshVars' env' pattern' ->
      Raw.Pi loc pattern' (fromFoilTerm freshVars env a) (Raw.AScopedTerm loc (fromFoilTerm freshVars' env' b))
  PairE t1 t2 -> Raw.Pair loc (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  FirstE t -> Raw.First loc (fromFoilTerm freshVars env t)
  SecondE t -> Raw.Second loc (fromFoilTerm freshVars env t)
  ProductE t1 t2 -> Raw.Product loc (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  UniverseE -> Raw.Universe loc
  where
    loc = error "location information is lost when converting from AST"

-- | Convert a /closed/ scope-safe term into a raw term.
fromFoilTermClosed
  :: [Raw.VarIdent]   -- ^ A stream of fresh variable identifiers.
  -> Expr VoidS       -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTermClosed freshVars = fromFoilTerm freshVars emptyNameMap

-- | Convert a scope-safe pattern into a raw pattern converting raw
-- identifiers directly into 'Raw.VarIdent'
fromFoilPattern'
  :: Pattern n l  -- ^ A scope-safe pattern that extends scope @n@ into scope @l@.
  -> Raw.Pattern
fromFoilPattern' pattern =
  case pattern of
    PatternWildcard -> Raw.PatternWildcard loc
    PatternVar z -> Raw.PatternVar loc (binderToVarIdent z)
    PatternPair l r ->
      let l' = fromFoilPattern' l
          r' = fromFoilPattern' r
       in Raw.PatternPair loc l' r'
    where
      loc = error "location information is lost when converting from AST"
      binderToVarIdent binder = Raw.VarIdent ("x" ++ show (nameId (nameOf binder)))

-- | Convert a scope-safe term into a raw term converting raw
-- identifiers directly into 'Raw.VarIdent'.
fromFoilTerm'
  :: Expr n                 -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTerm' = \case
  VarE name -> Raw.Var loc (nameToVarIdent name)
  AppE t1 t2 -> Raw.App loc (fromFoilTerm' t1) (fromFoilTerm' t2)
  LamE pattern body ->
    Raw.Lam loc (fromFoilPattern' pattern) (Raw.AScopedTerm loc (fromFoilTerm' body))
  PiE pattern a b ->
    Raw.Pi loc (fromFoilPattern' pattern) (fromFoilTerm' a) (Raw.AScopedTerm loc (fromFoilTerm' b))
  PairE t1 t2 -> Raw.Pair loc (fromFoilTerm' t1) (fromFoilTerm' t2)
  FirstE t -> Raw.First loc (fromFoilTerm' t)
  SecondE t -> Raw.Second loc (fromFoilTerm' t)
  ProductE t1 t2 -> Raw.Product loc (fromFoilTerm' t1) (fromFoilTerm' t2)
  UniverseE -> Raw.Universe loc
  where
    loc = error "location information is lost when converting from AST"
    nameToVarIdent name = Raw.VarIdent ("x" ++ show (nameId name))

-- * Evaluation

-- | Match a pattern against an expression.
matchPattern :: Pattern n l -> Expr n -> Substitution Expr l n
matchPattern pattern expr = go pattern expr identitySubst
  where
    go :: Pattern i l -> Expr n -> Substitution Expr i n -> Substitution Expr l n
    go PatternWildcard _   = id
    go (PatternVar x) e    = \subst -> addSubst subst x e
    go (PatternPair l r) e = go r (SecondE e) . go l (FirstE e)

-- | Compute weak head normal form (WHNF).
--
-- >>> whnf emptyScope "(λx.(λ_.x)(λy.x))(λy.λz.z)"
-- λ x0 . λ x1 . x1
--
-- >>> whnf emptyScope "(λs.λz.s(s(z)))(λs.λz.s(s(z)))"
-- λ x1 . (λ x0 . λ x1 . x0 (x0 x1)) ((λ x0 . λ x1 . x0 (x0 x1)) x1)
--
-- Note that during computation bound variables can become unordered
-- in the sense that binders may easily repeat or decrease. For example,
-- in the following expression, inner binder has lower index that the outer one:
--
-- >>> whnf emptyScope "(λx.λy.x)(λx.x)"
-- λ x1 . λ x0 . x0
--
-- At the same time, without substitution, we get regular, increasing binder indices:
--
-- >>> "λx.λy.y" :: Expr VoidS
-- λ x0 . λ x1 . x1
--
-- To compare terms for \(\alpha\)-equivalence, we may use 'alphaEquiv':
--
-- >>> alphaEquiv emptyScope (whnf emptyScope "(λx.λy.x)(λx.x)") "λx.λy.y"
-- True
--
-- We may also normalize binders using 'refreshExpr':
--
-- >>> refreshExpr emptyScope (whnf emptyScope "(λx.λy.x)(λx.x)")
-- λ x0 . λ x1 . x1
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE f arg ->
    case whnf scope f of
      LamE pat body ->
        let subst = matchPattern pat arg
         in whnf scope (substitute scope subst body)
      f' -> AppE f' arg
  FirstE t ->
    case whnf scope t of
      PairE l _r -> whnf scope l
      t'         -> FirstE t'
  SecondE t ->
    case whnf scope t of
      PairE _l r -> whnf scope r
      t'         -> SecondE t'
  t -> t

-- * \(\alpha\)-equivalence

-- | Normalize all binder identifiers in an expression.
refreshExpr :: Distinct n => Scope n -> Expr n -> Expr n
refreshExpr scope = substituteRefresh scope identitySubst

-- | \(\alpha\)-equivalence check for two terms in one scope
-- via normalization of bound identifiers (via 'refreshExpr').
--
-- This function may perform some unnecessary
-- changes of bound variables when the binders are the same on both sides.
alphaEquivRefreshed :: Distinct n => Scope n -> Expr n -> Expr n -> Bool
alphaEquivRefreshed scope e1 e2 =
  refreshExpr scope e1 `unsafeEqExpr` refreshExpr scope e2

-- | Unsafely check for equality of two 'Pattern's.
--
-- This __does not__ include \(\alpha\)-equivalence!
unsafeEqPattern :: Pattern n l -> Pattern n' l' -> Bool
unsafeEqPattern PatternWildcard PatternWildcard = True
unsafeEqPattern (PatternVar x) (PatternVar x')   = x == coerce x'
unsafeEqPattern (PatternPair l r) (PatternPair l' r') =
  unsafeEqPattern l l' && unsafeEqPattern r r'
unsafeEqPattern _ _ = False

-- | Unsafely check for equality of two 'Expr's.
--
-- This __does not__ include \(\alpha\)-equivalence!
unsafeEqExpr :: Expr n -> Expr l -> Bool
unsafeEqExpr e1 e2 = case (e1, e2) of
  (VarE x, VarE x')            -> x == coerce x'
  (AppE t1 t2, AppE t1' t2')   -> unsafeEqExpr t1 t1' && unsafeEqExpr t2 t2'
  (LamE x body, LamE x' body') -> unsafeEqPattern x x' && unsafeEqExpr body body'
  (PiE x a b, PiE x' a' b') -> unsafeEqPattern x x' && unsafeEqExpr a a' && unsafeEqExpr b b'
  (PairE l r, PairE l' r') -> unsafeEqExpr l l' && unsafeEqExpr r r'
  (FirstE t, FirstE t') -> unsafeEqExpr t t'
  (SecondE t, SecondE t') -> unsafeEqExpr t t'
  (ProductE l r, ProductE l' r') -> unsafeEqExpr l l' && unsafeEqExpr r r'
  (UniverseE, UniverseE) -> True
  _ -> False

-- | \(\alpha\)-equivalence check for two terms in one scope
-- via unification of bound variables (via 'unifyNameBinders').
--
-- Compared to 'alphaEquivRefreshed', this function might skip unnecessary
-- changes of bound variables when both binders in two matching scoped terms coincide.
alphaEquiv :: Distinct n => Scope n -> Expr n -> Expr n -> Bool
alphaEquiv scope e1 e2 = case (e1, e2) of
  (VarE x, VarE x') -> x == coerce x'
  (AppE t1 t2, AppE t1' t2') -> alphaEquiv scope t1 t1' && alphaEquiv scope t2 t2'
  (LamE x body, LamE x' body') -> case unifyPatterns x x' of
    SameNameBinders z    -> case assertDistinct z of
      Distinct -> alphaEquiv (extendScopePattern z scope) body body'
    RenameLeftNameBinder z renameL -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) body) body'
    RenameRightNameBinder z renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' body (liftRM scope' (fromNameBinderRenaming renameR) body')
    RenameBothBinders z renameL renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) body) (liftRM scope' (fromNameBinderRenaming renameR) body')
    NotUnifiable -> False
  (PiE x a b, PiE x' a' b') -> alphaEquiv scope a a' && case unifyPatterns x x' of
    SameNameBinders z    -> case assertDistinct z of Distinct -> alphaEquiv (extendScopePattern z scope) b b'
    RenameLeftNameBinder z renameL -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) b) b'
    RenameRightNameBinder z renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' b (liftRM scope' (fromNameBinderRenaming renameR) b')
    RenameBothBinders z renameL renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) b) (liftRM scope' (fromNameBinderRenaming renameR) b')
    NotUnifiable -> False
  (PairE l r, PairE l' r') -> alphaEquiv scope l l' && alphaEquiv scope r r'
  (FirstE t, FirstE t') -> alphaEquiv scope t t'
  (SecondE t, SecondE t') -> alphaEquiv scope t t'
  (ProductE l r, ProductE l' r') -> alphaEquiv scope l l' && alphaEquiv scope r r'
  (UniverseE, UniverseE) -> True
  _ -> False

-- * Interpreter

-- | Interpret a \(\lambda\Pi\) command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute _loc term _type) =
  putStrLn ("  ↦ " ++ printExpr (whnf emptyScope (toFoilTerm emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _loc _term _type) =
  putStrLn "Not yet implemented"

-- | Interpret a \(\lambda\Pi\) program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram _loc typedTerms) = mapM_ interpretCommand typedTerms

-- | Default interpreter program.
-- Reads a \(\lambda\Pi\) program from the standard input and runs the commands.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case pProgram (resolveLayout True (tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program

-- * Example terms

-- | A helper for constructing \(\lambda\)-abstractions.
lam :: Distinct n => Scope n -> (forall l. DExt n l => Scope l -> NameBinder n l -> Expr l) -> Expr n
lam scope mkBody = withFresh scope $ \x ->
  let scope' = extendScope x scope
   in LamE (PatternVar x) (mkBody scope' x)

-- | An identity function as a \(\lambda\)-term:
--
-- >>> identity
-- λ x0 . x0
identity :: Expr VoidS
identity = lam emptyScope $ \_ nx ->
  VarE (nameOf nx)

-- | Church-encoding of a natural number \(n\).
--
-- >>> churchN 0
-- λ x0 . λ x1 . x1
--
-- >>> churchN 3
-- λ x0 . λ x1 . x0 (x0 (x0 x1))
churchN :: Int -> Expr VoidS
churchN n =
  lam emptyScope $ \sx nx ->
    lam sx $ \_sxy ny ->
      let x = sink (VarE (nameOf nx))
          y = VarE (nameOf ny)
       in iterate (AppE x) y !! n
