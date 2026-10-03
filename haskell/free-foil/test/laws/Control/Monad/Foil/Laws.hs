{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Generators and law statements for the foil: scopes, renamings between
-- them, and the laws of 'Sinkable' and 'CoSinkable'.
--
-- The laws are those of @MAP-categorical-framework.md@ (§2, §5, §9.6).
--
-- 1. 'Sinkable' @e@ is a functor from scopes to sets, with
--    'sinkabilityProof' its action on renamings.
-- 2. 'CoSinkable' @p@ makes the projection of a pattern to the scope it
--    extends an opfibration: 'coSinkabilityProof' lifts a renaming of the
--    outer scope to a renaming of the inner one and a pushed pattern, and
--    the lift is functorial.
--
-- The generators are scope-safe by construction. Scopes grow from the
-- empty scope through 'withRefreshed', names are read off a scope, and a
-- binder that shadows a name of the ambient scope arises only the way it
-- arises in real code, by 'sink'ing a value built in an outer scope.
-- The generators use one unsafe ingredient, 'UnsafeName' for the /hint/
-- given to 'withRefreshed', which only decides which raw name a fresh
-- binder gets. (The law of 'unifyPatterns' also wraps a bound name back
-- into a binder to read off a verdict's renaming, as the library's own
-- 'Control.Monad.Free.Foil.alphaEquiv' does.)
--
-- Renamings are generated in three classes, so that a law can be checked
-- separately over each candidate base category of §9.2 of the map:
-- inclusions ('sink', i.e. thinnings), injective renamings, and arbitrary
-- renamings.
module Control.Monad.Foil.Laws (
  -- * Scopes
  Ctx (..),
  SomeCtx (..),
  ctxScope,
  withCtx,
  ctxChain,
  ctxNames,
  extendCtx,
  genHint,
  withHintedBinder,
  withHintedBinders,
  extendCtxBy,
  genCtx,
  genCtxAtLeast,
  showCtx,
  showName,
  -- * Patterns
  PatIn (..),
  GenPattern,
  genNameBinder,
  genNameBinderList,
  PatternNames,
  nameBinderNames,
  nameBinderListNames,
  patternRawNames,
  showPattern,
  showPatternWith,
  -- * Renamings
  Renaming (..),
  rename,
  identityRenaming,
  inclusionRenaming,
  composeRenaming,
  genFunction,
  genInjection,
  RenamingClass (..),
  allRenamingClasses,
  Includes (..),
  Chain' (..),
  Chain (..),
  genChain,
  showChain,
  -- * Laws of 'Sinkable'
  SinkableLaws (..),
  sinkableLaws,
  SinkLaw (..),
  SinkCase (..),
  genSinkCase,
  sinkableSpec,
  -- * Laws of 'CoSinkable'
  PatternCase (..),
  genPatternCase,
  CoSinkableLaws (..),
  coSinkableLaws,
  CoSinkLaw (..),
  coSinkableSpec,
  -- * Laws of 'UnifiablePattern'
  PatPair (..),
  GenPatternPair,
  genNameBinderListPair,
  unifyPatternsLaw,
  unifyPatternsSpec,
  -- * Running laws
  Verdict (..),
  law,
  extensionByCoercion,
  mergedBinderRenamings,
  genericCoSinkableCrash,
  genericPatternOrder,
) where

import           Control.Monad               (forM_)
import           Data.IntMap                 (IntMap)
import           Data.Kind                   (Type)
import qualified Data.IntMap                 as IntMap
import           Data.List                   (intercalate)
import           Test.Hspec
import           Test.Hspec.QuickCheck       (modifyMaxSuccess)
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Internal (Name (..), NameBinder (..))

-- * Scopes

-- | A scope together with the way it was reached from the empty scope.
-- Every step is a 'DExt', so a value built at any step can be 'sink'ed to
-- the end, and the chain of binders lets us build maps out of the scope
-- ('NameMap', 'Substitution').
data Ctx (n :: S) where
  Root  :: Ctx VoidS
  Under :: DExt m n => Ctx m -> NameBinderList m n -> Scope n -> Ctx n

-- | A context at an unknown scope.
data SomeCtx where
  SomeCtx :: Ctx n -> SomeCtx

-- | The scope a context ends at.
ctxScope :: Ctx n -> Scope n
ctxScope Root              = emptyScope
ctxScope (Under _ _ scope) = scope

-- | Every scope reached by a context is distinct.
withCtx :: Ctx n -> (Distinct n => Scope n -> r) -> r
withCtx Root k              = k emptyScope
withCtx (Under _ _ scope) k = k scope

-- | All binders from the empty scope to the end of the context.
ctxChain :: Ctx n -> NameBinderList VoidS n
ctxChain Root                  = NameBinderListEmpty
ctxChain (Under parent step _) = concatNameBinderLists (ctxChain parent) step

-- | The names of the scope, in the order in which they were bound.
ctxNames :: Ctx n -> [Name n]
ctxNames ctx = namesOfPattern (ctxChain ctx)

-- | Extend a context by a pattern.
extendCtx :: (CoSinkable p, DExt n l) => Ctx n -> p n l -> Ctx l
extendCtx ctx pat = withCtx ctx $ \scope ->
  Under ctx (nameBinderListOf pat) (extendScopePattern pat scope)

-- | A hint for 'withRefreshed'. The range is small, so hints often clash
-- with the scope and the binder falls back to a fresh name, and scopes are
-- not contiguous ranges of raw names.
genHint :: Gen Int
genHint = chooseInt (0, 15)

-- | Bind a name: the hint if it is free in the scope, and a fresh name
-- otherwise.
withHintedBinder
  :: Distinct n
  => Scope n
  -> (forall l. DExt n l => NameBinder n l -> Gen r)
  -> Gen r
withHintedBinder scope cont = do
  hint <- genHint
  withRefreshed scope (UnsafeName hint) cont

-- | Bind @k@ names, each one the hint if it is free in the scope and a
-- fresh name otherwise.
withHintedBinders
  :: Distinct n
  => Int -> Scope n
  -> (forall l. DExt n l => NameBinderList n l -> Gen r)
  -> Gen r
withHintedBinders k scope cont
  | k <= 0 = cont NameBinderListEmpty
  | otherwise =
      withHintedBinder scope $ \binder ->
        withHintedBinders (k - 1) (extendScope binder scope) $ \binders ->
          cont (NameBinderListCons binder binders)

-- | Extend a context by @k@ steps of one or two binders each.
extendCtxBy :: Int -> Ctx n -> (forall l. Ctx l -> Gen r) -> Gen r
extendCtxBy k ctx cont
  | k <= 0 = cont ctx
  | otherwise = withCtx ctx $ \scope -> do
      width <- chooseInt (1, 2)
      withHintedBinders width scope $ \binders ->
        extendCtxBy (k - 1) (extendCtx ctx binders) cont

-- | A context of up to four steps (up to eight names).
genCtx :: Gen SomeCtx
genCtx = do
  steps <- chooseInt (0, 4)
  extendCtxBy steps Root (pure . SomeCtx)

-- | A context with at least @k@ names, so that a renaming into it of the
-- required kind exists.
genCtxAtLeast :: Int -> Gen SomeCtx
genCtxAtLeast k = do
  SomeCtx ctx <- genCtx
  grow ctx
  where
    grow :: Ctx n -> Gen SomeCtx
    grow ctx
      | length (ctxNames ctx) >= k = pure (SomeCtx ctx)
      | otherwise = extendCtxBy 1 ctx grow

-- | Show the names of a scope.
showCtx :: Ctx n -> String
showCtx ctx = "{" <> intercalate ", " (map showName (ctxNames ctx)) <> "}"

-- | Show a name by its raw identifier.
showName :: Name n -> String
showName x = "x" <> show (nameId x)

-- * Patterns

-- | A pattern out of scope @n@, binding names fresh for @n@.
data PatIn p n where
  PatIn :: DExt n l => p n l -> PatIn p n

-- | A generator of patterns out of a given scope.
type GenPattern p = forall n. Ctx n -> Gen (PatIn p n)

-- | A single binder with a hinted name.
genNameBinder :: GenPattern NameBinder
genNameBinder ctx = withCtx ctx $ \scope -> withHintedBinder scope (pure . PatIn)

-- | Up to three binders with hinted names.
genNameBinderList :: GenPattern NameBinderList
genNameBinderList ctx = withCtx ctx $ \scope -> do
  k <- chooseInt (0, 3)
  withHintedBinders k scope (pure . PatIn)

-- | The raw names a pattern binds, in the order of its structure (left to
-- right). Each pattern type gives its own, since the library's traversal
-- ('patternRawNames') does not follow the structure for every type.
type PatternNames (p :: S -> S -> Type) = forall n l. p n l -> [Int]

-- | The name of a single binder.
nameBinderNames :: PatternNames NameBinder
nameBinderNames b = [nameId (nameOf b)]

-- | The names of a list of binders, in order.
nameBinderListNames :: PatternNames NameBinderList
nameBinderListNames = \case
  NameBinderListEmpty         -> []
  NameBinderListCons b rest -> nameId (nameOf b) : nameBinderListNames rest

-- | The raw names a pattern binds, in the order in which the library's
-- 'withPattern' visits them (through 'nameBinderListOf'). For a pattern
-- type with a hand-written 'withPattern' this is the order of the
-- structure. For the generic 'withPattern' it is the ascending order of
-- the raw names, since that goes through the unordered 'NameBinders'.
patternRawNames :: CoSinkable p => p n l -> [Int]
patternRawNames = nameBinderListNames . nameBinderListOf

-- | Show the names a pattern binds, in the library's order.
showPattern :: CoSinkable p => p n l -> String
showPattern = showPatternWith patternRawNames

-- | Show the names a pattern binds, in a given order.
showPatternWith :: PatternNames p -> p n l -> String
showPatternWith names pat = "[" <> unwords (map (("x" <>) . show) (names pat)) <> "]"

-- * Renamings

-- | A renaming of scope @n@ into scope @l@, as a finite table so that it
-- can be shown and composed. It is total on the names of the scope it was
-- generated for.
newtype Renaming (n :: S) (l :: S) = Renaming (IntMap (Name l))

instance Show (Renaming n l) where
  show (Renaming table) = "{" <> intercalate ", "
    [ "x" <> show x <> " ↦ " <> showName y | (x, y) <- IntMap.toList table ] <> "}"

-- | Apply a renaming.
rename :: Renaming n l -> Name n -> Name l
rename (Renaming table) x = case IntMap.lookup (nameId x) table of
  Just y  -> y
  Nothing -> error ("the renaming is not defined at " <> showName x)

-- | The identity renaming of a scope.
identityRenaming :: Ctx n -> Renaming n n
identityRenaming ctx = Renaming (IntMap.fromList [ (nameId x, x) | x <- ctxNames ctx ])

-- | The inclusion of a scope into an extension of it, i.e. 'sink'.
inclusionRenaming :: DExt n l => Ctx n -> Renaming n l
inclusionRenaming ctx = Renaming (IntMap.fromList [ (nameId x, sink x) | x <- ctxNames ctx ])

-- | Composition in diagrammatic order: first @f@, then @g@.
composeRenaming :: Renaming n l -> Renaming l k -> Renaming n k
composeRenaming (Renaming f) g = Renaming (fmap (rename g) f)

-- | An arbitrary renaming. The target must have a name if the source has.
genFunction :: Ctx n -> Ctx l -> Gen (Renaming n l)
genFunction from to = do
  let targets = ctxNames to
  pairs <- mapM (\x -> (,) (nameId x) <$> elements targets) (ctxNames from)
  pure (Renaming (IntMap.fromList pairs))

-- | An injective renaming. The target must have at least as many names as
-- the source.
genInjection :: Ctx n -> Ctx l -> Gen (Renaming n l)
genInjection from to = do
  targets <- shuffle (ctxNames to)
  pure (Renaming (IntMap.fromList (zip (map nameId (ctxNames from)) targets)))

-- | The three classes of renamings, i.e. the three candidate base
-- categories of §9.2 of the map.
data RenamingClass
  = Inclusions  -- ^ Thinnings: the identity on raw names, as 'sink' does.
  | Injections  -- ^ Injective renamings (the category \(\mathbb{I}\)).
  | Functions   -- ^ All renamings (the category \(\mathbb{F}\)).
  deriving (Eq, Show, Enum, Bounded)

-- | All classes, smallest first.
allRenamingClasses :: [RenamingClass]
allRenamingClasses = [minBound .. maxBound]

-- | Evidence that the second scope extends the first.
data Includes (n :: S) (l :: S) where
  Includes :: DExt n l => Includes n l

-- | Three scopes and two composable renamings between them, of one class,
-- starting at scope @n@. For 'Inclusions' each scope extends the previous
-- one, and the evidence for the first step is kept.
data Chain' (n :: S) where
  Chain'
    :: Ctx n -> Ctx l -> Ctx k
    -> Renaming n l -> Renaming l k
    -> Maybe (Includes n l)
    -> Chain' n

-- | A 'Chain'' starting at an unknown scope.
data Chain where
  Chain :: Chain' n -> Chain

-- | Generate a 'Chain' of the given class.
genChain :: RenamingClass -> Gen Chain
genChain cls = do
  SomeCtx n <- genCtx
  case cls of
    Inclusions -> withCtx n $ \_ -> do
      k1 <- chooseInt (0, 2)
      k2 <- chooseInt (0, 2)
      extendBy k1 n $ \l -> extendBy k2 l $ \k ->
        pure (Chain (Chain' n l k (inclusionRenaming n) (inclusionRenaming l) (Just Includes)))
    Injections -> do
      SomeCtx l <- genCtxAtLeast (length (ctxNames n))
      SomeCtx k <- genCtxAtLeast (length (ctxNames l))
      f <- genInjection n l
      g <- genInjection l k
      pure (Chain (Chain' n l k f g Nothing))
    Functions -> do
      SomeCtx l <- genCtxAtLeast (min 1 (length (ctxNames n)))
      SomeCtx k <- genCtxAtLeast (min 1 (length (ctxNames l)))
      f <- genFunction n l
      g <- genFunction l k
      pure (Chain (Chain' n l k f g Nothing))
  where
    -- 'extendCtxBy' with the inclusion visible to the continuation.
    extendBy :: Distinct n => Int -> Ctx n -> (forall l. DExt n l => Ctx l -> Gen r) -> Gen r
    extendBy steps ctx cont
      | steps <= 0 = cont ctx
      | otherwise = do
          width <- chooseInt (1, 2)
          withHintedBinders width (ctxScope ctx) $ \binders ->
            let ctx' = extendCtx ctx binders
             in extendBy (steps - 1) ctx' cont

-- | Show the scopes and renamings of a chain.
showChain :: Chain' n -> String
showChain (Chain' n l k f g _) = unlines
  [ "n = " <> showCtx n, "l = " <> showCtx l, "k = " <> showCtx k
  , "f : n → l = " <> show f, "g : l → k = " <> show g ]

-- * Laws of 'Sinkable'

-- | The laws of a 'Sinkable' type @e@, read as a functor from scopes to
-- sets. The equality is a parameter, since for terms it is α-equivalence.
data SinkableLaws e = SinkableLaws
  { -- | @sinkabilityProof id = id@.
    sinkIdentity    :: forall n. Ctx n -> e n -> Property
    -- | @sinkabilityProof (g . f) = sinkabilityProof g . sinkabilityProof f@.
  , sinkComposition :: forall n l k. Ctx k -> Renaming n l -> Renaming l k -> e n -> Property
    -- | On an inclusion, @sinkabilityProof sink = sink@: the coercion that
    -- 'sink' performs is the action of the functor (§2 of the map).
  , sinkInclusion   :: forall n l. Includes n l -> Ctx l -> e n -> Property
  }

-- | The laws, for a given equality and printer.
sinkableLaws
  :: Sinkable e
  => (forall n. Ctx n -> e n -> e n -> Bool)
  -> (forall n. e n -> String)
  -> SinkableLaws e
sinkableLaws eq showE = SinkableLaws
  { sinkIdentity = \ctx t ->
      let lhs = sinkabilityProof id t
       in counterexample ("sinkabilityProof id t = " <> showE lhs) (eq ctx lhs t)
  , sinkComposition = \ctxK f g t ->
      let lhs = sinkabilityProof (rename g . rename f) t
          rhs = sinkabilityProof (rename g) (sinkabilityProof (rename f) t)
       in counterexample ("sinkabilityProof (g . f) t = " <> showE lhs) $
            counterexample ("sinkabilityProof g (sinkabilityProof f t) = " <> showE rhs) $
              eq ctxK lhs rhs
  , sinkInclusion = \Includes ctxL t ->
      let lhs = sinkabilityProof sink t
          rhs = sink t
       in counterexample ("sinkabilityProof sink t = " <> showE lhs) $
            counterexample ("sink t = " <> showE rhs) $
              eq ctxL lhs rhs
  }

-- | The laws of 'SinkableLaws', by name.
data SinkLaw = SinkIdentity | SinkComposition | SinkInclusion
  deriving (Eq, Show, Enum, Bounded)

-- | A value in the first scope of a chain.
data SinkCase e where
  SinkCase :: Chain' n -> e n -> SinkCase e

-- | A chain of the given class with a value in its first scope.
genSinkCase :: (forall n. Ctx n -> Gen (e n)) -> RenamingClass -> Gen (SinkCase e)
genSinkCase genE cls = do
  Chain chain@(Chain' n _ _ _ _ _) <- genChain cls
  SinkCase chain <$> genE n

-- | The laws of 'Sinkable' for one type: the identity law once, and the
-- composition law along each class of renamings. The inclusion law is
-- checked along inclusions only.
sinkableSpec
  :: Sinkable e
  => (forall n. Ctx n -> e n -> e n -> Bool)   -- ^ Equality.
  -> (forall n. e n -> String)                 -- ^ Printer.
  -> (forall n. Ctx n -> Gen (e n))            -- ^ Generator.
  -> (forall n. e n -> [e n])                  -- ^ Shrinker.
  -> (RenamingClass -> SinkLaw -> Verdict)
  -> Spec
sinkableSpec eq showE genE shrinkE verdict = do
  let laws = sinkableLaws eq showE
      cases cls = forAllShrinkShow (genSinkCase genE cls) shrinkCase showCase
      shrinkCase (SinkCase chain t) = map (SinkCase chain) (shrinkE t)
      showCase (SinkCase chain t) = showChain chain <> "t = " <> showE t
  law (verdict Inclusions SinkIdentity) (show SinkIdentity) $
    cases Inclusions $ \(SinkCase (Chain' n _ _ _ _ _) t) -> sinkIdentity laws n t
  forM_ allRenamingClasses $ \cls -> describe ("along " <> show cls) $ do
    law (verdict cls SinkComposition) (show SinkComposition) $
      cases cls $ \(SinkCase (Chain' _ _ k f g _) t) -> sinkComposition laws k f g t
    case cls of
      Inclusions -> law (verdict cls SinkInclusion) (show SinkInclusion) $
        cases cls $ \(SinkCase (Chain' _ l _ _ _ incl) t) -> case incl of
          Just evidence -> sinkInclusion laws evidence l t
          Nothing       -> property Discard
      _ -> pure ()

-- * Laws of 'CoSinkable'

-- | A pattern out of the first scope of a chain.
data PatternCase p where
  PatternCase :: DExt n i => Chain' n -> p n i -> PatternCase p

-- | Show a 'PatternCase'.
showPatternCase :: PatternNames p -> PatternCase p -> String
showPatternCase names (PatternCase chain p) = showChain chain <> "p : n → i = " <> showPatternWith names p

-- | A chain of the given class with a pattern out of its first scope.
genPatternCase :: GenPattern p -> RenamingClass -> Gen (PatternCase p)
genPatternCase genPat cls = do
  Chain chain@(Chain' n _ _ _ _ _) <- genChain cls
  PatIn pat <- genPat n
  pure (PatternCase chain pat)

-- | The laws of 'coSinkabilityProof', reading a pattern type as a span
-- (§5 of the map). Each law is stated on a pattern @p : n → i@ and the
-- renamings @f : n → l@ and @g : l → k@ of a 'PatternCase'. Write
-- @(f', p')@ for the result of @coSinkabilityProof f p@: the extended
-- renaming @f' : i → i'@ and the pushed pattern @p' : l → i'@.
data CoSinkableLaws p = CoSinkableLaws
  { -- | Pushing along the identity changes nothing: @p' = p@ and @f' = id@.
    coSinkIdentity    :: PatternCase p -> Property
    -- | Pushing along @g . f@ is pushing along @f@ and then along @g@: the
    -- pushed patterns agree and the extended renamings compose.
  , coSinkComposition :: PatternCase p -> Property
    -- | The extended renaming extends @f@: @f' (sink x) = f x@ for every
    -- name @x@ of @n@, i.e. the square of scopes commutes. The map does not
    -- spell this out, but it is what makes @(f, f')@ a morphism of spans,
    -- and the documentation of 'coSinkabilityProof' calls @f'@ an
    -- /extended/ renaming.
  , coSinkExtension   :: PatternCase p -> Property
    -- | The extended renaming sends the binders of @p@ to the binders of
    -- @p'@, in order.
  , coSinkBinders     :: PatternCase p -> Property
  }

-- | The laws of 'coSinkabilityProof' for any 'CoSinkable' pattern type.
-- Names in different scopes are compared by their raw identifiers, and the
-- binders of a pattern are listed by the given function.
coSinkableLaws :: CoSinkable p => PatternNames p -> CoSinkableLaws p
coSinkableLaws binders = CoSinkableLaws
  { coSinkIdentity = \(PatternCase (Chain' n _ _ _ _ _) p) ->
      coSinkabilityProof id p $ \f' p' ->
        let xs = namesUnder n p
         in counterexample ("pushed pattern p' = " <> showPatternWith binders p') $
              counterexample ("f' on i = " <> showOn f' xs) $
                binders p' === binders p
                  .&&. map (nameId . f') xs === map nameId xs
  , coSinkComposition = \(PatternCase (Chain' n _ _ f g _) p) ->
      coSinkabilityProof (rename g . rename f) p $ \h q ->
        coSinkabilityProof (rename f) p $ \f' p' ->
          coSinkabilityProof (rename g) p' $ \g' p'' ->
            let xs = namesUnder n p
             in counterexample ("pushed along g . f: " <> showPatternWith binders q) $
                  counterexample ("pushed along f, then g: " <> showPatternWith binders p'') $
                    counterexample ("(g . f)' on i = " <> showOn h xs) $
                      counterexample ("g' . f' on i = " <> showOn (g' . f') xs) $
                        binders q === binders p''
                          .&&. map (nameId . h) xs === map (nameId . g' . f') xs
  , coSinkExtension = \(PatternCase (Chain' n _ _ f _ _) p) ->
      coSinkabilityProof (rename f) p $ \f' _p' ->
        let outer = ctxNames n
         in counterexample ("f' on n = " <> showOn (f' . sink) outer) $
              map (nameId . f' . sink) outer === map (nameId . rename f) outer
  , coSinkBinders = \(PatternCase (Chain' _ _ _ f _ _) p) ->
      coSinkabilityProof (rename f) p $ \f' p' ->
        counterexample ("pushed pattern p' = " <> showPatternWith binders p') $
          map (nameId . f' . UnsafeName) (binders p) === binders p'
  }
  where
    -- The names of the scope a pattern extends to: the outer ones, then
    -- the bound ones.
    namesUnder :: (CoSinkable p, DExt n i) => Ctx n -> p n i -> [Name i]
    namesUnder n p = ctxNames (extendCtx n p)

    showOn :: (Name a -> Name b) -> [Name a] -> String
    showOn h xs = "{" <> intercalate ", " [ showName x <> " ↦ " <> showName (h x) | x <- xs ] <> "}"

-- | The laws of 'CoSinkableLaws', by name, and the law of the traversal
-- order of 'withPattern'.
data CoSinkLaw
  = CoSinkIdentity | CoSinkComposition | CoSinkExtension | CoSinkBinders
  | WithPatternOrder
  deriving (Eq, Show, Enum, Bounded)

-- | 'withPattern' visits the binders of a pattern in the order of its
-- structure. Everything that pairs the binders of a pattern with other
-- data relies on this: 'addSubstPattern' pairs them with terms,
-- 'nameBinderListOf' lists them, and 'withRefreshedPattern' puts the
-- refreshed names back.
withPatternOrderLaw :: CoSinkable p => PatternNames p -> p n l -> Property
withPatternOrderLaw binders p =
  counterexample "the order of the pattern is on the left, the order of withPattern on the right" $
    binders p === patternRawNames p

-- | All laws of 'coSinkabilityProof' for a pattern type, along each class
-- of renamings, and the law of the traversal order of 'withPattern'.
coSinkableSpec
  :: CoSinkable p
  => PatternNames p -> GenPattern p -> (RenamingClass -> CoSinkLaw -> Verdict) -> Spec
coSinkableSpec binders genPat verdict = do
  law (verdict Inclusions WithPatternOrder) "withPattern visits binders in the order of the pattern" $
    forAllShow (genPatternCase genPat Inclusions) (showPatternCase binders) $
      \(PatternCase _ p) -> withPatternOrderLaw binders p
  forM_ allRenamingClasses $ \cls -> describe ("along " <> show cls) $
    forM_ [CoSinkIdentity, CoSinkComposition, CoSinkExtension, CoSinkBinders] $ \name ->
      law (verdict cls name) (show name) $
        forAllShow (genPatternCase genPat cls) (showPatternCase binders) (lawOf name)
  where
    laws = coSinkableLaws binders
    lawOf CoSinkIdentity    = coSinkIdentity laws
    lawOf CoSinkComposition = coSinkComposition laws
    lawOf CoSinkExtension   = coSinkExtension laws
    lawOf CoSinkBinders     = coSinkBinders laws
    lawOf WithPatternOrder  = \(PatternCase _ p) -> withPatternOrderLaw binders p

-- * Laws of 'UnifiablePattern'

-- | Two patterns out of the same scope, which bind the same number of names.
data PatPair p n where
  PatPair :: (DExt n l, DExt n r) => p n l -> p n r -> PatPair p n

-- | A generator of pairs of patterns of the same shape.
type GenPatternPair p = forall n. Ctx n -> Gen (PatPair p n)

-- | Two lists of the same length, of up to three hinted binders each.
genNameBinderListPair :: GenPatternPair NameBinderList
genNameBinderListPair ctx = withCtx ctx $ \scope -> do
  k <- chooseInt (0, 3)
  withHintedBinders k scope $ \l ->
    withHintedBinders k scope $ \r -> pure (PatPair l r)

-- | The verdict of 'unifyPatternsIn' on two patterns of the same shape
-- pairs their binders position by position: the renamings it prescribes
-- send the @j@-th binder of each side to one and the same name, and
-- distinct positions to distinct names. This is the reading of
-- 'UnifiablePattern' as equality in the quotient of §4 and §5 of the map
-- (the default instance compares "the number and order of binders").
unifyPatternsLaw :: UnifiablePattern p => PatternNames p -> Ctx n -> PatPair p n -> Property
unifyPatternsLaw binders ctx (PatPair l r) = withCtx ctx $ \scope ->
  let xs = binders l
      ys = binders r
      positional us vs =
        counterexample ("left binders become " <> show us) $
          counterexample ("right binders become " <> show vs) $
            us === vs .&&. counterexample "two positions are merged" (distinct us)
   in counterexample ("left pattern = " <> showPatternWith binders l) $
        counterexample ("right pattern = " <> showPatternWith binders r) $
          case unifyPatternsIn scope l r of
            SameNameBinders _ ->
              counterexample "SameNameBinders" $ positional xs ys
            RenameLeftNameBinder _ f ->
              counterexample "RenameLeftNameBinder" $ positional (map (renamed f) xs) ys
            RenameRightNameBinder _ g ->
              counterexample "RenameRightNameBinder" $ positional xs (map (renamed g) ys)
            RenameBothBinders _ f g ->
              counterexample "RenameBothBinders" $ positional (map (renamed f) xs) (map (renamed g) ys)
            NotUnifiable ->
              counterexample "NotUnifiable" False
  where
    -- The name a binder renaming assigns to a bound name.
    renamed :: (NameBinder a b -> NameBinder a c) -> Int -> Int
    renamed f x = nameId (nameOf (f (UnsafeNameBinder (UnsafeName x))))
    distinct us = and [ u /= v | (i, u) <- zip [0 :: Int ..] us, (j, v) <- zip [0 :: Int ..] us, i < j ]

-- | The positional law of 'unifyPatternsIn' on pairs of patterns.
unifyPatternsSpec :: UnifiablePattern p => PatternNames p -> GenPatternPair p -> Verdict -> Spec
unifyPatternsSpec binders genPair verdict =
  law verdict "unifyPatternsIn pairs binders position by position" $
    forAllShow (genSomePair genPair) showSomePair $ \(SomePair ctx pair) -> unifyPatternsLaw binders ctx pair
  where
    showSomePair (SomePair ctx _) = "n = " <> showCtx ctx

-- | A pair of patterns out of an unknown scope.
data SomePair p where
  SomePair :: Ctx n -> PatPair p n -> SomePair p

genSomePair :: GenPatternPair p -> Gen (SomePair p)
genSomePair genPair = do
  SomeCtx ctx <- genCtx
  SomePair ctx <$> genPair ctx

-- * Running laws

-- | What we expect of a law.
data Verdict
  = Holds
    -- | The law fails at the moment. The test checks that it still fails
    -- (with 'expectFailure'), so that the suite notices when it is fixed.
    -- Some counterexamples are rare (one case in a few thousand), so the
    -- search for one may run up to 50000 cases; it stops at the first.
  | KnownFailure String
    -- | The law fails, but so rarely that neither 'Holds' nor 'KnownFailure'
    -- gives a reliable test. It is checked on 1000 cases, and a
    -- counterexample is reported as pending rather than as a failure.
  | Unstable String

-- | The verdicts for a pattern type whose 'coSinkabilityProof' hands back a
-- coercion as the extended renaming, as the instances for 'NameBinder',
-- 'NameBinders' and (through them) 'NameBinderList' do. Such a renaming
-- extends @f@ only when @f@ is the identity on raw names, i.e. an inclusion.
extensionByCoercion :: RenamingClass -> CoSinkLaw -> Verdict
extensionByCoercion Inclusions _ = Holds
extensionByCoercion _ CoSinkExtension = KnownFailure
  "the extended renaming is a coercion, so it extends f only when f is an inclusion"
extensionByCoercion _ _ = Holds

-- | The verdict for 'unifyPatterns' on patterns of several binders, which
-- go through the instance for 'NameBinderList'.
mergedBinderRenamings :: Verdict
mergedBinderRenamings = KnownFailure
  "unsafeMergeUnifyBinders composes the renamings of successive binders, so a chain of them collapses"

-- | The verdict for 'coSinkabilityProof' of a pattern type whose instance
-- is the generic default, which goes through 'SinkableK' 'NameBinder'.
genericCoSinkableCrash :: Verdict
genericCoSinkableCrash = KnownFailure
  "the generic coSinkabilityProof crashes on a binder: SinkableK NameBinder matches one renaming, a binder has two indices"

-- | The verdict for laws that go through the generic 'withPattern' (the
-- default for a pattern type with 'HasNameBinders') on patterns of several
-- binders.
genericPatternOrder :: Verdict
genericPatternOrder = KnownFailure
  "the generic withPattern visits binders in ascending order of raw names and puts them back in that order"

-- | Check a law on at least 1000 cases, or pin it as a known failure.
law :: Testable p => Verdict -> String -> p -> Spec
law Holds name p =
  modifyMaxSuccess (max 1000) (it name (property p))
law (KnownFailure why) name p =
  it (name <> " (known failure: " <> why <> ")") (expectFailure (withMaxSuccess 50000 p))
law (Unstable why) name p =
  it (name <> " (unstable: " <> why <> ")") $ do
    result <- quickCheckWithResult stdArgs { maxSuccess = 1000, chatty = False } p
    case result of
      Success{} -> pure ()
      _         -> pendingWith ("counterexample found, as expected at times:\n" <> output result)
