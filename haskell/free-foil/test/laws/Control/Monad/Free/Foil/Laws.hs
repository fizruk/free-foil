{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Generators of scope-safe terms of any free foil signature, and the laws
-- of the relative monad @'AST' binder sig@ on 'Name', in the sense of
-- Altenkirch, Chapman and Uustalu, with unit 'Var' and bind 'substitute'
-- (and 'rbind').
--
-- A language plugs in with a 'SyntaxGen': the shapes of its nodes (with
-- @()@ in place of subterms), a generator of its patterns, and a printer
-- for its nodes. 'genAST' fills the shapes, at every step choosing between
-- building a subterm here and building it in an outer scope of the context
-- and 'sink'ing it. The latter is how real code produces binders that
-- shadow names of the ambient scope, and it is what exercises
-- capture-avoidance in 'substitute'.
module Control.Monad.Free.Foil.Laws (
  -- * Terms
  SyntaxGen (..),
  genAST,
  shrinkAST,
  mutations,
  hasShadowing,
  boundNames,
  showAST,
  showNodeVia,
  -- * α-equivalence
  alphaEqNameless,
  AlphaLaw (..),
  alphaSpec,
  PairCase (..),
  genPairCase,
  showPairCase,
  genericSinkableCrash,
  -- * Substitutions
  SubstKind (..),
  Subst (..),
  genSubstInto,
  showSubst,
  composeSubst,
  explicitIdentitySubst,
  -- * Test cases
  TermCase (..),
  genTermCase,
  shrinkTermCase,
  showTermCase,
  SubstCase (..),
  genSubstCase,
  shrinkSubstCase,
  showSubstCase,
  RenamingCase (..),
  genRenamingCase,
  shrinkRenamingCase,
  showRenamingCase,
  -- * Laws of the relative monad
  RelMonadLaws (..),
  relMonadLaws,
  RelMonadLaw (..),
  relMonadSpec,
  -- * Functoriality of terms
  FunctorLaws (..),
  functorLaws,
  FunctorLaw (..),
  functorSpec,
) where

import           Control.Monad               (forM_, guard)
import           Data.Bifoldable             (bifoldr)
import           Data.Bifunctor              (Bifunctor, bimap)
import           Data.Bitraversable          (Bitraversable, bitraverse)
import qualified Data.IntMap                 as IntMap
import           Data.IntSet                 (IntSet)
import qualified Data.IntSet                 as IntSet
import           Data.List                   (intercalate)
import           Data.Maybe                  (isJust)
import           Test.Hspec                  (Spec, describe)
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Laws
import           Control.Monad.Foil.Relative (RelMonad (..), liftRM)
import           Control.Monad.Free.Foil
import           Data.ZipMatchK              (ZipMatchK, zipMatchWith2)

-- * Terms

-- | What 'genAST' needs to know about a language.
data SyntaxGen binder sig = SyntaxGen
  { -- | The shapes of the nodes. A shape with no holes is a leaf. When a
    -- scope has no names and the signature has no leaves, a shape whose
    -- holes are all scoped is used, so its patterns must bind something.
    sgShapes   :: [sig () ()]
    -- | Patterns out of a given scope.
  , sgPattern  :: GenPattern binder
    -- | The names a pattern binds, in the order of its structure.
  , sgPatternNames :: PatternNames binder
    -- | Print a node whose subterms are already printed.
  , sgShowNode :: sig String String -> String
  }

-- | The number of scoped and of unscoped holes of a node.
holes :: Bitraversable sig => sig a b -> (Int, Int)
holes = bifoldr (\_ (s, t) -> (s + 1, t)) (\_ (s, t) -> (s, t + 1)) (0, 0)

-- | A term of about the given size in the scope of the context.
genAST
  :: forall binder sig n. (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> Ctx n -> Int -> Gen (AST binder sig n)
genAST sg ctx size = case ctx of
  Under parent _ _ | size > 0 ->
    frequency [ (1, sink <$> genAST sg parent size), (6, here) ]
  _ -> here
  where
    vars = ctxNames ctx
    shapes = sgShapes sg
    leaves = [ s | s <- shapes, holes s == (0, 0) ]
    nodes = [ s | s <- shapes, holes s /= (0, 0) ]
    binding = [ s | s <- nodes, snd (holes s) == 0 ]

    here
      | size <= 0 = case (vars, leaves) of
          ([], []) -> elements binding >>= fill 0
          _ -> oneof $
            [ Var <$> elements vars | not (null vars) ] ++
            [ elements leaves >>= fill 0 | not (null leaves) ]
      | otherwise = frequency $
          [ (2, Var <$> elements vars) | not (null vars) ] ++
          [ (1, elements leaves >>= fill 0) | not (null leaves) ] ++
          [ (6, elements nodes >>= fill (size - 1)) | not (null nodes) ]

    fill :: Int -> sig () () -> Gen (AST binder sig n)
    fill budget shape =
      let (s, t) = holes shape
          each = budget `div` max 1 (s + t)
       in Node <$> bitraverse (\() -> genScoped each) (\() -> genAST sg ctx each) shape

    genScoped :: Int -> Gen (ScopedAST binder sig n)
    genScoped each = do
      PatIn pat <- sgPattern sg ctx
      ScopedAST pat <$> genAST sg (extendCtx ctx pat) each

-- | Shrink a term within its scope: replace a node by one of its unscoped
-- subterms, or shrink one subterm (under its binder if it is scoped).
shrinkAST :: forall binder sig n. Bitraversable sig => AST binder sig n -> [AST binder sig n]
shrinkAST = \case
  Var _ -> []
  Node node -> unscopedChildren node ++ map Node (shrinkOne node)
  where
    unscopedChildren = bifoldr (\_ acc -> acc) (:) []

    shrinkOne :: forall x. sig (ScopedAST binder sig x) (AST binder sig x) -> [sig (ScopedAST binder sig x) (AST binder sig x)]
    shrinkOne = alterOneHole shrinkScoped shrinkAST

    shrinkScoped :: forall x. ScopedAST binder sig x -> [ScopedAST binder sig x]
    shrinkScoped (ScopedAST pat body) = [ ScopedAST pat body' | body' <- shrinkAST body ]

-- | All nodes that differ from the given one in exactly one subterm, given
-- the alternatives for each kind of subterm.
alterOneHole
  :: Bitraversable sig
  => (s -> [s]) -> (t -> [t]) -> sig s t -> [sig s t]
alterOneHole onScoped onTerm node = concat
  [ fst (runAt (bitraverse (at i onScoped) (at i onTerm) node) 0)
  | i <- [0 .. uncurry (+) (holes node) - 1] ]
  where
    -- At the @i@-th hole, the alternatives for the subterm; elsewhere, the
    -- subterm itself.
    at :: Int -> (a -> [a]) -> a -> At a
    at i alts x = At $ \j -> (if i == j then alts x else [x], j + 1)

-- | All terms that differ from the given one in exactly one occurrence of a
-- variable, replaced by another name in scope at that point. Most of them
-- are not α-equivalent to the original, which makes them good test cases
-- for an α-equivalence check.
mutations
  :: forall binder sig n. (Bitraversable sig, CoSinkable binder, Distinct n)
  => [Name n] -> AST binder sig n -> [AST binder sig n]
mutations names = \case
  Var x -> [ Var y | y <- names, y /= x ]
  Node node -> map Node (alterOneHole scoped (mutations names) node)
  where
    scoped :: ScopedAST binder sig n -> [ScopedAST binder sig n]
    scoped (ScopedAST pat body) = case (assertDistinct pat, assertExt pat) of
      (Distinct, Ext) ->
        [ ScopedAST pat body' | body' <- mutations (map sink names ++ namesOfPattern pat) body ]

-- | Whether some binder of the term binds a name that is already in scope
-- at that point, given the raw names of the scope of the term. Such binders
-- arise from 'sink' and are what capture-avoidance has to handle.
hasShadowing :: (Bitraversable sig, CoSinkable binder) => IntSet -> AST binder sig n -> Bool
hasShadowing scope = \case
  Var _ -> False
  Node node -> bifoldr (\s acc -> scoped s || acc) (\t acc -> hasShadowing scope t || acc) False node
  where
    scoped (ScopedAST pat body) =
      let names = patternRawNames pat
       in any (`IntSet.member` scope) names
            || hasShadowing (IntSet.union scope (IntSet.fromList names)) body

-- | The raw names bound anywhere in a term.
boundNames :: (Bitraversable sig, CoSinkable binder) => AST binder sig n -> IntSet
boundNames = \case
  Var _ -> IntSet.empty
  Node node -> bifoldr (\s acc -> scoped s <> acc) (\t acc -> boundNames t <> acc) IntSet.empty node
  where
    scoped (ScopedAST pat body) = IntSet.fromList (patternRawNames pat) <> boundNames body

-- | The raw names of a context.
ctxRawNames :: Ctx n -> IntSet
ctxRawNames = IntSet.fromList . map nameId . ctxNames

-- | Label a test case of a term in a context by whether it shadows.
termCoverage :: (Bitraversable sig, CoSinkable binder) => Ctx n -> AST binder sig n -> Property -> Property
termCoverage n t = classify (hasShadowing (ctxRawNames n) t) "t has a shadowing binder"

-- | Label a test case of substitution by whether the term shadows, and by
-- whether one of its binders is a name of the target scope, so that
-- 'substitute' has to rename it.
substCoverage :: (Bitraversable sig, CoSinkable binder) => SubstCase binder sig -> Property -> Property
substCoverage (SubstCase i o1 _ _ _ t) =
  termCoverage i t
    . classify (not (IntSet.disjoint (boundNames t) (ctxRawNames o1))) "a binder of t is a name of o1"

-- | An applicative that numbers the holes of a traversal and collects the
-- alternatives at each of them.
newtype At a = At { runAt :: Int -> ([a], Int) }

instance Functor At where
  fmap f (At g) = At $ \j -> let (xs, j') = g j in (map f xs, j')

instance Applicative At where
  pure x = At $ \j -> ([x], j)
  At f <*> At x = At $ \j ->
    let (fs, j') = f j
        (xs, j'') = x j'
     in ([ g y | g <- fs, y <- xs ], j'')

-- | Print a term with raw names (@x3@), and scoped terms as @λ[x3 x4]. t@.
showAST :: Bifunctor sig => SyntaxGen binder sig -> AST binder sig n -> String
showAST sg = \case
  Var x -> showName x
  Node node -> sgShowNode sg (bimap showScoped (showAST sg) node)
  where
    showScoped (ScopedAST pat body) = "λ" <> showPatternWith (sgPatternNames sg) pat <> ". " <> showAST sg body

-- | A node printer from a derived 'Show' instance. The subterms are shown
-- verbatim, in parentheses when they contain a space.
showNodeVia :: (Bifunctor sig, Show (sig Shown Shown)) => sig String String -> String
showNodeVia = show . bimap Shown Shown

-- | A string that 'show' prints as it is.
newtype Shown = Shown String

instance Show Shown where
  showsPrec d (Shown s)
    | d > 10 && ' ' `elem` s = showString ("(" <> s <> ")")
    | otherwise = showString s

-- * Substitutions

-- | How a substitution is built.
data SubstKind
  = Total  -- ^ Every name of the domain is mapped explicitly, into an unrelated scope.
  | Beta   -- ^ The domain extends the codomain by some binders, and only these
           --   are mapped ('addSubstList' on 'identitySubst'), as in a β-reduction.
  deriving (Eq, Show, Enum, Bounded)

-- | A substitution together with its explicit entries, for printing.
data Subst binder sig i o = Subst
  { substKind  :: SubstKind
  , substValue :: Substitution (AST binder sig) i o
  , substTable :: [(Name i, AST binder sig o)]
  }

-- | Show the explicit entries of a substitution.
showSubst :: Bifunctor sig => SyntaxGen binder sig -> Subst binder sig i o -> String
showSubst sg s = show (substKind s) <> " {" <> intercalate ", "
  [ showName x <> " ↦ " <> showAST sg t | (x, t) <- substTable s ] <> "}"

-- | Generate a substitution into the given scope, and its domain. A 'Total'
-- substitution comes from an independent scope, a 'Beta' one from an
-- extension of the codomain.
genSubstInto
  :: (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> SubstKind -> Ctx o
  -> (forall i. Ctx i -> Subst binder sig i o -> Gen r) -> Gen r
genSubstInto sg kind o cont = case kind of
  Total -> do
    SomeCtx i <- genCtx
    ts <- mapM (const (genAST sg o 4)) (ctxNames i)
    let value = nameMapToSubstitution (addNameBinderList (ctxChain i) ts emptyNameMap)
    cont i (Subst Total value (zip (ctxNames i) ts))
  Beta -> withCtx o $ \scope -> do
    k <- chooseInt (1, 3)
    withHintedBinders k scope $ \binders -> do
      ts <- mapM (const (genAST sg o 4)) (namesOfPattern binders)
      let value = addSubstList identitySubst binders ts
      cont (extendCtx o binders) (Subst Beta value (zip (namesOfPattern binders) ts))

-- | Kleisli composition @s2 ⊙ s1@: substitute with @s1@, then with @s2@.
-- The result maps every name of @i@ explicitly.
composeSubst
  :: (Bifunctor sig, CoSinkable binder, SinkableK binder, Distinct o2)
  => Ctx i -> Scope o2
  -> Substitution (AST binder sig) i o1
  -> Substitution (AST binder sig) o1 o2
  -> Substitution (AST binder sig) i o2
composeSubst i scope2 s1 s2 =
  nameMapToSubstitution $ addNameBinderList (ctxChain i)
    [ substitute scope2 s2 (lookupSubst s1 x) | x <- ctxNames i ] emptyNameMap

-- | The identity substitution with every name mapped explicitly, so that
-- 'substitute' cannot take its shortcut for the empty substitution.
explicitIdentitySubst :: Ctx n -> Substitution (AST binder sig) n n
explicitIdentitySubst n =
  nameMapToSubstitution (addNameBinderList (ctxChain n) (map Var (ctxNames n)) emptyNameMap)

-- * Test cases

-- | A term in a scope.
data TermCase binder sig where
  TermCase :: Ctx n -> AST binder sig n -> TermCase binder sig

-- | A term in a random scope.
genTermCase
  :: (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> Gen (TermCase binder sig)
genTermCase sg = do
  SomeCtx n <- genCtx
  TermCase n <$> sized (genAST sg n . min 30)

-- | Shrink the term of a 'TermCase'.
shrinkTermCase :: Bitraversable sig => TermCase binder sig -> [TermCase binder sig]
shrinkTermCase (TermCase n t) = map (TermCase n) (shrinkAST t)

-- | Show a 'TermCase'.
showTermCase :: Bifunctor sig => SyntaxGen binder sig -> TermCase binder sig -> String
showTermCase sg (TermCase n t) = unlines [ "n = " <> showCtx n, "t = " <> showAST sg t ]

-- | Two composable substitutions and a term: @t : i@, @s1 : i → o1@ and
-- @s2 : o1 → o2@.
data SubstCase binder sig where
  SubstCase
    :: Ctx i -> Ctx o1 -> Ctx o2
    -> Subst binder sig i o1 -> Subst binder sig o1 o2
    -> AST binder sig i
    -> SubstCase binder sig

-- | Generate a 'SubstCase' with substitutions of the given kinds.
genSubstCase
  :: (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> SubstKind -> SubstKind -> Gen (SubstCase binder sig)
genSubstCase sg kind1 kind2 = do
  SomeCtx o2 <- genCtx
  genSubstInto sg kind2 o2 $ \o1 s2 ->
    genSubstInto sg kind1 o1 $ \i s1 -> do
      t <- sized (genAST sg i . min 30)
      pure (SubstCase i o1 o2 s1 s2 t)

-- | Shrink the term of a 'SubstCase'.
shrinkSubstCase :: Bitraversable sig => SubstCase binder sig -> [SubstCase binder sig]
shrinkSubstCase (SubstCase i o1 o2 s1 s2 t) = map (SubstCase i o1 o2 s1 s2) (shrinkAST t)

-- | Show a 'SubstCase'.
showSubstCase :: Bifunctor sig => SyntaxGen binder sig -> SubstCase binder sig -> String
showSubstCase sg (SubstCase i o1 o2 s1 s2 t) = unlines
  [ "i = " <> showCtx i, "o1 = " <> showCtx o1, "o2 = " <> showCtx o2
  , "s1 : i → o1 = " <> showSubst sg s1
  , "s2 : o1 → o2 = " <> showSubst sg s2
  , "t = " <> showAST sg t ]

-- | A chain of renamings and a term in its first scope.
data RenamingCase binder sig where
  RenamingCase :: Chain' n -> AST binder sig n -> RenamingCase binder sig

-- | Generate a 'RenamingCase' of the given class.
genRenamingCase
  :: (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> RenamingClass -> Gen (RenamingCase binder sig)
genRenamingCase sg cls = do
  Chain chain@(Chain' n _ _ _ _ _) <- genChain cls
  RenamingCase chain <$> sized (genAST sg n . min 30)

-- | Shrink the term of a 'RenamingCase'.
shrinkRenamingCase :: Bitraversable sig => RenamingCase binder sig -> [RenamingCase binder sig]
shrinkRenamingCase (RenamingCase chain t) = map (RenamingCase chain) (shrinkAST t)

-- | Show a 'RenamingCase'.
showRenamingCase :: Bifunctor sig => SyntaxGen binder sig -> RenamingCase binder sig -> String
showRenamingCase sg (RenamingCase chain t) = showChain chain <> "t = " <> showAST sg t

-- * Laws of the relative monad

-- | 'rbind' at 'Name', the unit of the relative monad of terms.
rbindN
  :: (Bifunctor sig, CoSinkable binder, SinkableK binder, Distinct b)
  => Scope b -> AST binder sig a -> (Name a -> AST binder sig b) -> AST binder sig b
rbindN = rbind

-- | 'rreturn' at 'Name'.
rreturnN
  :: (Bifunctor sig, CoSinkable binder, SinkableK binder)
  => Name a -> AST binder sig a
rreturnN = rreturn

-- | 'liftRM' at 'Name'.
liftRMN
  :: (Bifunctor sig, CoSinkable binder, SinkableK binder, Distinct b)
  => Scope b -> (Name a -> Name b) -> AST binder sig a -> AST binder sig b
liftRMN = liftRM

-- | The laws of 'substitute' and of 'rbind', up to α-equivalence.
data RelMonadLaws binder sig = RelMonadLaws
  { -- | Left unit: @substitute o s (Var x) = lookupSubst s x@.
    substLeftUnit             :: SubstCase binder sig -> Property
    -- | Right unit: @substitute n identitySubst t ≡α t@.
  , substRightUnit            :: TermCase binder sig -> Property
    -- | Right unit, with every name mapped explicitly (so no shortcut).
  , substRightUnitExplicit    :: TermCase binder sig -> Property
    -- | Associativity:
    -- @substitute o2 s2 (substitute o1 s1 t) ≡α substitute o2 (s2 ⊙ s1) t@.
  , substAssociativity        :: SubstCase binder sig -> Property
    -- | Left unit of 'rbind': @rbind o (rreturn x) f = f x@.
  , rbindLeftUnit             :: SubstCase binder sig -> Property
    -- | Right unit of 'rbind': @rbind n t rreturn ≡α t@.
  , rbindRightUnit            :: TermCase binder sig -> Property
    -- | Associativity of 'rbind'.
  , rbindAssociativity        :: SubstCase binder sig -> Property
    -- | 'substitute' and 'rbind' are the same Kleisli extension.
  , substituteAgreesWithRbind :: SubstCase binder sig -> Property
  }

-- | The laws for a language, with α-equivalence ('alphaEquiv') as the
-- equality.
relMonadLaws
  :: forall binder sig.
     (Bitraversable sig, ZipMatchK sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> RelMonadLaws binder sig
relMonadLaws sg = RelMonadLaws
  { substLeftUnit = \(SubstCase i o1 _ s1 _ _) -> withCtx o1 $ \scope1 ->
      conjoin
        [ cmp scope1
            "substitute o1 s1 (Var x)" (substitute scope1 (substValue s1) (Var x))
            "lookupSubst s1 x" (lookupSubst (substValue s1) x)
        | x <- ctxNames i ]
  , substRightUnit = \(TermCase n t) -> withCtx n $ \scope ->
      cmp scope "substitute n identitySubst t" (substitute scope identitySubst t) "t" t
  , substRightUnitExplicit = \(TermCase n t) -> withCtx n $ \scope ->
      cmp scope
        "substitute n (explicit identity) t" (substitute scope (explicitIdentitySubst n) t)
        "t" t
  , substAssociativity = \(SubstCase i o1 o2 s1 s2 t) ->
      withCtx o1 $ \scope1 -> withCtx o2 $ \scope2 ->
        cmp scope2
          "substitute o2 s2 (substitute o1 s1 t)"
          (substitute scope2 (substValue s2) (substitute scope1 (substValue s1) t))
          "substitute o2 (s2 ⊙ s1) t"
          (substitute scope2 (composeSubst i scope2 (substValue s1) (substValue s2)) t)
  , rbindLeftUnit = \(SubstCase i o1 _ s1 _ _) -> withCtx o1 $ \scope1 ->
      conjoin
        [ cmp scope1
            "rbind o1 (rreturn x) f" (rbindN scope1 (rreturnN x) (lookupSubst (substValue s1)))
            "f x" (lookupSubst (substValue s1) x)
        | x <- ctxNames i ]
  , rbindRightUnit = \(TermCase n t) -> withCtx n $ \scope ->
      cmp scope "rbind n t rreturn" (rbindN scope t rreturnN) "t" t
  , rbindAssociativity = \(SubstCase _ o1 o2 s1 s2 t) ->
      withCtx o1 $ \scope1 -> withCtx o2 $ \scope2 ->
        let f = lookupSubst (substValue s1)
            g = lookupSubst (substValue s2)
         in cmp scope2
              "rbind o2 (rbind o1 t f) g" (rbindN scope2 (rbindN scope1 t f) g)
              "rbind o2 t (\\x -> rbind o2 (f x) g)" (rbindN scope2 t (\x -> rbindN scope2 (f x) g))
  , substituteAgreesWithRbind = \(SubstCase _ o1 _ s1 _ t) -> withCtx o1 $ \scope1 ->
      cmp scope1
        "substitute o1 s1 t" (substitute scope1 (substValue s1) t)
        "rbind o1 t (lookupSubst s1)" (rbindN scope1 t (lookupSubst (substValue s1)))
  }
  where
    cmp :: Scope x -> String -> AST binder sig x -> String -> AST binder sig x -> Property
    cmp = compareUpToAlpha sg

-- | Compare two terms up to α-equivalence, printing both on failure. The
-- comparison is 'alphaEqNameless' and not the library's 'alphaEquiv',
-- which gets patterns of two or more binders wrong (see 'alphaSpec').
compareUpToAlpha
  :: (Bitraversable sig, ZipMatchK sig)
  => SyntaxGen binder sig
  -> Scope x -> String -> AST binder sig x -> String -> AST binder sig x -> Property
compareUpToAlpha sg _scope lhsName lhs rhsName rhs =
  counterexample (lhsName <> " = " <> showAST sg lhs) $
    counterexample (rhsName <> " = " <> showAST sg rhs) $
      alphaEqNameless (sgPatternNames sg) lhs rhs

-- * Functoriality of terms

-- | Two ways of renaming terms: the 'Sinkable' instance, and 'liftRM',
-- which goes through 'rbind'.
data FunctorLaws binder sig = FunctorLaws
  { -- | The functor laws of 'sinkabilityProof' on terms, up to α.
    termSinkableLaws      :: SinkableLaws (AST binder sig)
    -- | @liftRM n id t ≡α t@.
  , liftRMIdentity        :: TermCase binder sig -> Property
    -- | @liftRM k (g . f) t ≡α liftRM k g (liftRM l f t)@.
  , liftRMComposition     :: RenamingCase binder sig -> Property
    -- | @liftRM l sink t ≡α sink t@ on an inclusion.
  , liftRMInclusion       :: RenamingCase binder sig -> Property
    -- | @sinkabilityProof f t ≡α liftRM l f t@: the action of the functor
    -- 'Sinkable' agrees with the one derived from the relative monad.
  , sinkAgreesWithLiftRM  :: RenamingCase binder sig -> Property
  }

-- | The functor laws for a language.
functorLaws
  :: forall binder sig.
     (Bitraversable sig, ZipMatchK sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> FunctorLaws binder sig
functorLaws sg = FunctorLaws
  { termSinkableLaws =
      sinkableLaws (\_ a b -> alphaEqNameless (sgPatternNames sg) a b) (showAST sg)
  , liftRMIdentity = \(TermCase n t) -> withCtx n $ \scope ->
      cmp scope "liftRM n id t" (liftRMN scope id t) "t" t
  , liftRMComposition = \(RenamingCase (Chain' _ l k f g _) t) ->
      withCtx l $ \scopeL -> withCtx k $ \scopeK ->
        cmp scopeK
          "liftRM k (g . f) t" (liftRMN scopeK (rename g . rename f) t)
          "liftRM k g (liftRM l f t)" (liftRMN scopeK (rename g) (liftRMN scopeL (rename f) t))
  , liftRMInclusion = \(RenamingCase (Chain' _ l _ _ _ incl) t) -> case incl of
      Nothing -> property Discard
      Just Includes -> withCtx l $ \scopeL ->
        cmp scopeL "liftRM l sink t" (liftRMN scopeL sink t) "sink t" (sink t)
  , sinkAgreesWithLiftRM = \(RenamingCase (Chain' _ l _ f _ _) t) -> withCtx l $ \scopeL ->
      cmp scopeL
        "sinkabilityProof f t" (sinkabilityProof (rename f) t)
        "liftRM l f t" (liftRMN scopeL (rename f) t)
  }
  where
    cmp :: Scope x -> String -> AST binder sig x -> String -> AST binder sig x -> Property
    cmp = compareUpToAlpha sg

-- * Running the laws

-- | The laws of 'RelMonadLaws', by name.
data RelMonadLaw
  = SubstLeftUnit | SubstRightUnit | SubstRightUnitExplicit | SubstAssociativity
  | RbindLeftUnit | RbindRightUnit | RbindAssociativity | SubstituteAgreesWithRbind
  deriving (Eq, Show, Enum, Bounded)

-- | All relative monad laws for a language. The laws on substitutions are
-- checked for each combination of 'SubstKind's, which the verdict is given
-- (it is given 'Nothing' for the laws on terms).
relMonadSpec
  :: (Bitraversable sig, ZipMatchK sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> (RelMonadLaw -> Maybe (SubstKind, SubstKind) -> Verdict) -> Spec
relMonadSpec sg verdict = do
  let laws = relMonadLaws sg
      onTerms name p = law (verdict name Nothing) (show name) $
        forAllShrinkShow (genTermCase sg) shrinkTermCase (showTermCase sg) $ \c@(TermCase n t) ->
          termCoverage n t (p c)
      onSubsts name p = describe (show name) $
        forM_ [ (k1, k2) | k1 <- [minBound .. maxBound], k2 <- [minBound .. maxBound] ] $ \(k1, k2) ->
          law (verdict name (Just (k1, k2))) ("s1 " <> show k1 <> ", s2 " <> show k2) $
            forAllShrinkShow (genSubstCase sg k1 k2) shrinkSubstCase (showSubstCase sg) $ \c ->
              substCoverage c (p c)
  onSubsts SubstLeftUnit (substLeftUnit laws)
  onTerms SubstRightUnit (substRightUnit laws)
  onTerms SubstRightUnitExplicit (substRightUnitExplicit laws)
  onSubsts SubstAssociativity (substAssociativity laws)
  onSubsts RbindLeftUnit (rbindLeftUnit laws)
  onTerms RbindRightUnit (rbindRightUnit laws)
  onSubsts RbindAssociativity (rbindAssociativity laws)
  onSubsts SubstituteAgreesWithRbind (substituteAgreesWithRbind laws)

-- | The laws of 'FunctorLaws' other than those of 'SinkableLaws', by name.
data FunctorLaw = LiftRMIdentity | LiftRMComposition | LiftRMInclusion | SinkAgreesWithLiftRM
  deriving (Eq, Show, Enum, Bounded)

-- | The functor laws of terms: 'sinkabilityProof', 'liftRM', and their
-- agreement, along each class of renamings.
functorSpec
  :: (Bitraversable sig, ZipMatchK sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig
  -> (RenamingClass -> SinkLaw -> Verdict)
  -> (RenamingClass -> FunctorLaw -> Verdict)
  -> Spec
functorSpec sg sinkVerdict verdict = do
  let laws = functorLaws sg
      onRenamings cls name p = law (verdict cls name) (show name) $
        forAllShrinkShow (genRenamingCase sg cls) shrinkRenamingCase (showRenamingCase sg) $
          \c@(RenamingCase (Chain' n _ _ _ _ _) t) -> termCoverage n t (p c)
  describe "sinkabilityProof" $
    sinkableSpec
      (\_ a b -> alphaEqNameless (sgPatternNames sg) a b)
      (showAST sg)
      (\ctx -> sized (genAST sg ctx . min 30))
      shrinkAST
      sinkVerdict
  describe "liftRM" $ do
    law (verdict Inclusions LiftRMIdentity) (show LiftRMIdentity) $
      forAllShrinkShow (genTermCase sg) shrinkTermCase (showTermCase sg) (liftRMIdentity laws)
    forM_ allRenamingClasses $ \cls -> describe ("along " <> show cls) $ do
      onRenamings cls LiftRMComposition (liftRMComposition laws)
      case cls of
        Inclusions -> onRenamings cls LiftRMInclusion (liftRMInclusion laws)
        _          -> pure ()
  describe "sinkabilityProof and liftRM" $
    forM_ allRenamingClasses $ \cls -> describe ("along " <> show cls) $
      onRenamings cls SinkAgreesWithLiftRM (sinkAgreesWithLiftRM laws)

-- * α-equivalence

-- | α-equivalence by a nameless comparison, independent of the library's
-- 'unifyPatterns'. A bound name is compared by the position of its binder
-- (a level counted along the path from the root, binder by binder), and a
-- free name by its raw identifier. Patterns are compared up to their
-- binders, i.e. by the number of names they bind, as the default
-- 'unifyPatterns' does. The binders of a pattern are listed in the order
-- of its structure, by the given function.
alphaEqNameless
  :: forall binder sig x y. (Bitraversable sig, ZipMatchK sig)
  => PatternNames binder -> AST binder sig x -> AST binder sig y -> Bool
alphaEqNameless binders = go 0 IntMap.empty IntMap.empty
  where
    go :: Int -> IntMap.IntMap Int -> IntMap.IntMap Int -> AST binder sig a -> AST binder sig b -> Bool
    go _ envL envR (Var a) (Var b) =
      case (IntMap.lookup (nameId a) envL, IntMap.lookup (nameId b) envR) of
        (Just i, Just j)   -> i == j
        (Nothing, Nothing) -> nameId a == nameId b
        _                  -> False
    go lvl envL envR (Node l) (Node r) = isJust $
      zipMatchWith2
        (\a b -> guard (scoped lvl envL envR a b))
        (\a b -> guard (go lvl envL envR a b))
        l r
    go _ _ _ _ _ = False

    scoped :: Int -> IntMap.IntMap Int -> IntMap.IntMap Int -> ScopedAST binder sig a -> ScopedAST binder sig b -> Bool
    scoped lvl envL envR (ScopedAST p body1) (ScopedAST q body2) =
      let xs = binders p
          ys = binders q
          k = length xs
          bind env names = foldl (\e (name, i) -> IntMap.insert name i e) env (zip names [lvl ..])
       in length ys == k && go (lvl + k) (bind envL xs) (bind envR ys) body1 body2

-- | The verdict for 'sinkabilityProof' on terms whose 'Sinkable' instance
-- is the generic one, through 'SinkableK' 'NameBinder'.
genericSinkableCrash :: Verdict
genericSinkableCrash = KnownFailure
  "the generic sinkabilityProof crashes on a binder: SinkableK NameBinder matches one renaming, a binder has two indices"

-- | Checks of the library's α-equivalence against 'alphaEqNameless'.
data AlphaLaw
  = AlphaEquivRefreshed'  -- ^ @alphaEquiv n t (refreshAST n t)@: completeness on an α-variant.
  | AlphaEquivAgrees      -- ^ @alphaEquiv@ agrees with 'alphaEqNameless'.
  | AlphaEquivRefreshedAgrees  -- ^ @alphaEquivRefreshed@ agrees with 'alphaEqNameless'.
  deriving (Eq, Show, Enum, Bounded)

-- | A term and a variant of it: an α-variant ('refreshAST'), or an
-- α-variant with one variable occurrence changed.
data PairCase binder sig where
  PairCase :: Ctx n -> AST binder sig n -> AST binder sig n -> PairCase binder sig

genPairCase
  :: (Bitraversable sig, CoSinkable binder, SinkableK binder)
  => SyntaxGen binder sig -> Gen (PairCase binder sig)
genPairCase sg = do
  SomeCtx n <- genCtx
  withCtx n $ \scope -> do
    t <- sized (genAST sg n . min 30)
    let t' = refreshAST scope t
    mutate <- arbitrary
    t'' <- case mutations (ctxNames n) t' of
      ts@(_ : _) | mutate -> elements ts
      _                   -> pure t'
    pure (PairCase n t t'')

-- | The library's α-equivalence checks against 'alphaEqNameless'.
alphaSpec
  :: (Bitraversable sig, ZipMatchK sig, UnifiablePattern binder, SinkableK binder)
  => SyntaxGen binder sig -> (AlphaLaw -> Verdict) -> Spec
alphaSpec sg verdict = do
  law (verdict AlphaEquivRefreshed') "alphaEquiv n t (refreshAST n t)" $
    forAllShrinkShow (genTermCase sg) shrinkTermCase (showTermCase sg) $ \(TermCase n t) ->
      withCtx n $ \scope ->
        counterexample ("refreshAST n t = " <> showAST sg (refreshAST scope t)) $
          alphaEquiv scope t (refreshAST scope t)
  law (verdict AlphaEquivAgrees) "alphaEquiv agrees with a nameless comparison" $
    forAllShow (genPairCase sg) (showPairCase sg) $ \(PairCase n t1 t2) ->
      withCtx n $ \scope -> alphaEquiv scope t1 t2 === alphaEqNameless (sgPatternNames sg) t1 t2
  law (verdict AlphaEquivRefreshedAgrees) "alphaEquivRefreshed agrees with a nameless comparison" $
    forAllShow (genPairCase sg) (showPairCase sg) $ \(PairCase n t1 t2) ->
      withCtx n $ \scope -> alphaEquivRefreshed scope t1 t2 === alphaEqNameless (sgPatternNames sg) t1 t2

-- | Show a 'PairCase'.
showPairCase :: Bifunctor sig => SyntaxGen binder sig -> PairCase binder sig -> String
showPairCase sg (PairCase n t1 t2) = unlines
  [ "n = " <> showCtx n, "t1 = " <> showAST sg t1, "t2 = " <> showAST sg t2 ]
