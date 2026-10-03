{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The laws for a language written with the plain foil (no free monad),
-- tested through a /mirror/: a free foil syntax with the same constructors.
-- Terms are generated as mirror terms and converted, and compared by
-- converting back and using 'alphaEqNameless'.
--
-- The laws are those of "Control.Monad.Free.Foil.Laws", for the
-- language's own 'Sinkable' instance, relative monad ('rbind'),
-- 'substitute' and α-equivalence.
module Control.Monad.Free.Foil.Laws.Mirror (
  Mirror (..),
  AlphaEquivOf (..),
  MirrorLaw (..),
  mirrorSpec,
) where

import           Control.Monad                (forM_)
import           Data.Bitraversable           (Bitraversable)
import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Internal  (Substitution (..))
import           Control.Monad.Foil.Laws
import           Control.Monad.Foil.Relative  (RelMonad, liftRM, rbind, rreturn)
import           Control.Monad.Free.Foil      (AST, refreshAST)
import           Control.Monad.Free.Foil.Laws
import           Data.ZipMatchK               (ZipMatchK)

-- | A plain foil language @e@ and its free foil mirror.
data Mirror binder sig e = Mirror
  { mirrorSyntax     :: SyntaxGen binder sig
    -- | From the mirror.
  , mirrorFrom       :: forall n. AST binder sig n -> e n
    -- | To the mirror.
  , mirrorTo         :: forall n. e n -> AST binder sig n
    -- | The language's 'substitute'.
  , mirrorSubstitute :: forall i o. Distinct o => Scope o -> Substitution e i o -> e i -> e o
    -- | The language's α-equivalence, if it has one.
  , mirrorAlphaEquiv :: Maybe (AlphaEquivOf e)
  }

-- | An α-equivalence check of a language.
newtype AlphaEquivOf e = AlphaEquivOf (forall n. Distinct n => Scope n -> e n -> e n -> Bool)

-- | The laws checked by 'mirrorSpec', by name.
data MirrorLaw
  = MirrorSinkable SinkLaw
  | MirrorLiftRMIdentity
  | MirrorLiftRMComposition
  | MirrorSinkAgreesWithLiftRM
  | MirrorSubstLeftUnit
  | MirrorSubstRightUnit
  | MirrorSubstRightUnitExplicit
  | MirrorSubstAssociativity
  | MirrorRbindRightUnit
  | MirrorRbindAssociativity
  | MirrorSubstituteAgreesWithRbind
  | MirrorAlphaEquivRefresh
  | MirrorAlphaEquivAgrees
  deriving (Eq, Show)

-- | Convert the values of a substitution.
mapSubst :: (e o -> e' o) -> Substitution e i o -> Substitution e' i o
mapSubst f (UnsafeSubstitution env) = UnsafeSubstitution (fmap f env)

-- | All the laws for a plain foil language, given a verdict for each law
-- along each class of renamings (the class is 'Inclusions' for the laws
-- that take no renaming).
mirrorSpec
  :: forall binder sig e.
     ( Bitraversable sig, ZipMatchK sig, UnifiablePattern binder, SinkableK binder
     , Sinkable e, InjectName e, RelMonad Name e )
  => Mirror binder sig e
  -> (RenamingClass -> MirrorLaw -> Verdict)
  -> Spec
mirrorSpec m verdict = do
  describe "Sinkable" $
    sinkableSpec (const eqE) showE
      (\ctx -> from <$> sized (genAST sg ctx . min 30))
      (map from . shrinkAST . to)
      (\cls name -> verdict cls (MirrorSinkable name))

  describe "liftRM (through rbind)" $ do
    onTerms MirrorLiftRMIdentity "liftRM n id t ≡α t" $ \n t -> withCtx n $ \scope ->
      cmp "liftRM n id t" (liftRME scope id t) "t" t
    onRenamings MirrorLiftRMComposition "liftRM k (g . f) t ≡α liftRM k g (liftRM l f t)" $
      \(Chain' _ l k f g _) t -> withCtx l $ \scopeL -> withCtx k $ \scopeK ->
        cmp "liftRM k (g . f) t" (liftRME scopeK (rename g . rename f) t)
            "liftRM k g (liftRM l f t)" (liftRME scopeK (rename g) (liftRME scopeL (rename f) t))

  describe "sinkabilityProof and liftRM" $
    onRenamings MirrorSinkAgreesWithLiftRM "sinkabilityProof f t ≡α liftRM l f t" $
      \(Chain' _ l _ f _ _) t -> withCtx l $ \scopeL ->
        cmp "sinkabilityProof f t" (sinkabilityProof (rename f) t)
            "liftRM l f t" (liftRME scopeL (rename f) t)

  describe "substitute" $ do
    onSubsts MirrorSubstLeftUnit "left unit" $ \i scope1 _ s1 _ _ ->
      conjoin [ cmp "substitute o1 s1 x" (subst scope1 s1 (injectName x))
                    "lookupSubst s1 x" (lookupSubst s1 x)
              | x <- ctxNames i ]
    onTerms MirrorSubstRightUnit "right unit" $ \n t -> withCtx n $ \scope ->
      cmp "substitute n identitySubst t" (subst scope identitySubst t) "t" t
    onTerms MirrorSubstRightUnitExplicit "right unit (explicit identity)" $ \n t -> withCtx n $ \scope ->
      cmp "substitute n (explicit identity) t" (subst scope (explicitIdentity n) t) "t" t
    onSubsts MirrorSubstAssociativity "associativity" $ \i scope1 scope2 s1 s2 t ->
      let composite = nameMapToSubstitution $ addNameBinderList (ctxChain i)
            [ subst scope2 s2 (lookupSubst s1 x) | x <- ctxNames i ] emptyNameMap
       in cmp "substitute o2 s2 (substitute o1 s1 t)" (subst scope2 s2 (subst scope1 s1 t))
              "substitute o2 (s2 ⊙ s1) t" (subst scope2 composite t)

  describe "rbind" $ do
    onTerms MirrorRbindRightUnit "right unit" $ \n t -> withCtx n $ \scope ->
      cmp "rbind n t rreturn" (rbindE scope t rreturnE) "t" t
    onSubsts MirrorRbindAssociativity "associativity" $ \_ scope1 scope2 s1 s2 t ->
      let f = lookupSubst s1
          g = lookupSubst s2
       in cmp "rbind o2 (rbind o1 t f) g" (rbindE scope2 (rbindE scope1 t f) g)
              "rbind o2 t (\\x -> rbind o2 (f x) g)" (rbindE scope2 t (\x -> rbindE scope2 (f x) g))
    onSubsts MirrorSubstituteAgreesWithRbind "agrees with substitute" $ \_ scope1 _ s1 _ t ->
      cmp "substitute o1 s1 t" (subst scope1 s1 t)
          "rbind o1 t (lookupSubst s1)" (rbindE scope1 t (lookupSubst s1))

  case mirrorAlphaEquiv m of
    Nothing -> pure ()
    Just (AlphaEquivOf alphaEquivE) -> describe "α-equivalence" $ do
      onTerms MirrorAlphaEquivRefresh "alphaEquiv n t t' for an α-variant t' (refreshAST of the mirror)" $
        \n t -> withCtx n $ \scope ->
          let t' = from (refreshAST scope (to t))
           in counterexample ("t' = " <> showE t') $
                alphaEquivE scope t t'
      law (verdict Inclusions MirrorAlphaEquivAgrees) "alphaEquiv agrees with a nameless comparison" $
        forAllShow (genPairCase sg) (showPairCase sg) $ \(PairCase n t1 t2) -> withCtx n $ \scope ->
          alphaEquivE scope (from t1) (from t2) === alphaEqNameless (sgPatternNames sg) t1 t2
  where
    sg = mirrorSyntax m
    from :: AST binder sig n -> e n
    from = mirrorFrom m
    to :: e n -> AST binder sig n
    to = mirrorTo m
    subst :: Distinct o => Scope o -> Substitution e i o -> e i -> e o
    subst = mirrorSubstitute m

    showE :: e n -> String
    showE = showAST sg . to

    eqE :: e n -> e n -> Bool
    eqE a b = alphaEqNameless (sgPatternNames sg) (to a) (to b)

    cmp :: String -> e n -> String -> e n -> Property
    cmp lhsName lhs rhsName rhs =
      counterexample (lhsName <> " = " <> showE lhs) $
        counterexample (rhsName <> " = " <> showE rhs) $
          eqE lhs rhs

    rbindE :: Distinct o => Scope o -> e i -> (Name i -> e o) -> e o
    rbindE = rbind

    rreturnE :: Name n -> e n
    rreturnE = rreturn

    liftRME :: Distinct o => Scope o -> (Name i -> Name o) -> e i -> e o
    liftRME = liftRM

    explicitIdentity :: Ctx n -> Substitution e n n
    explicitIdentity n =
      nameMapToSubstitution (addNameBinderList (ctxChain n) (map injectName (ctxNames n)) emptyNameMap)

    onTerms :: MirrorLaw -> String -> (forall n. Ctx n -> e n -> Property) -> Spec
    onTerms name title p = law (verdict Inclusions name) title $
      forAllShrinkShow (genTermCase sg) shrinkTermCase (showTermCase sg) $ \(TermCase n t) ->
        p n (from t)

    onRenamings :: MirrorLaw -> String -> (forall n. Chain' n -> e n -> Property) -> Spec
    onRenamings name title p = forM_ allRenamingClasses $ \cls ->
      describe ("along " <> show cls) $ law (verdict cls name) title $
        forAllShrinkShow (genRenamingCase sg cls) shrinkRenamingCase (showRenamingCase sg) $
          \(RenamingCase chain t) -> p chain (from t)

    onSubsts
      :: MirrorLaw -> String
      -> (forall i o1 o2. (Distinct o1, Distinct o2)
            => Ctx i -> Scope o1 -> Scope o2
            -> Substitution e i o1 -> Substitution e o1 o2
            -> e i -> Property)
      -> Spec
    onSubsts name title p = describe title $
      forM_ [ (k1, k2) | k1 <- [minBound .. maxBound], k2 <- [minBound .. maxBound] ] $ \(k1, k2) ->
        law (verdict Inclusions name) ("s1 " <> show k1 <> ", s2 " <> show k2) $
          forAllShrinkShow (genSubstCase sg k1 k2) shrinkSubstCase (showSubstCase sg) $
            \(SubstCase i o1 o2 s1 s2 t) -> withCtx o1 $ \scope1 -> withCtx o2 $ \scope2 ->
              p i scope1 scope2
                (mapSubst from (substValue s1)) (mapSubst from (substValue s2)) (from t)
