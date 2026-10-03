{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
-- | The laws for the λ-calculus of "Control.Monad.Foil.Example", the plain
-- foil without the free monad: its hand-written 'Foil.Sinkable' instance,
-- its relative monad ('rbind'), and its 'substitute'.
--
-- Terms are generated and compared through the free foil version of the
-- same language, which has the same constructors.
module Control.Monad.Foil.ExampleLawsSpec (spec) where

import           Control.Monad                         (forM_)
import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Foil
import qualified Control.Monad.Foil.Example            as F
import           Control.Monad.Foil.Internal           (Substitution (..))
import           Control.Monad.Foil.Laws
import           Control.Monad.Foil.Relative           (liftRM, rbind, rreturn)
import           Control.Monad.Free.Foil               (AST (..))
import qualified Control.Monad.Free.Foil.Example       as FF
import           Control.Monad.Free.Foil.ExampleSyntax (exprSyntax)
import           Control.Monad.Free.Foil.Laws

-- | The free foil term with the same structure.
toAST :: F.Expr n -> FF.Expr n
toAST = \case
  F.VarE x      -> Var x
  F.AppE f x    -> FF.AppE (toAST f) (toAST x)
  F.LamE b body -> FF.LamE b (toAST body)

-- | The plain foil term with the same structure.
fromAST :: FF.Expr n -> F.Expr n
fromAST = \case
  Var x         -> F.VarE x
  FF.AppE f x   -> F.AppE (fromAST f) (fromAST x)
  FF.LamE b body -> F.LamE b (fromAST body)

-- | Convert the values of a substitution.
mapSubst :: (e o -> e' o) -> Substitution e i o -> Substitution e' i o
mapSubst f (UnsafeSubstitution env) = UnsafeSubstitution (fmap f env)

sg :: SyntaxGen NameBinder FF.ExprF
sg = exprSyntax genNameBinder

-- | Equality up to α, through the free foil term.
eqE :: F.Expr n -> F.Expr n -> Bool
eqE a b = alphaEqNameless (toAST a) (toAST b)

-- | Compare two terms, printing both on failure.
cmp :: String -> F.Expr n -> String -> F.Expr n -> Property
cmp lhsName lhs rhsName rhs =
  counterexample (lhsName <> " = " <> show lhs) $
    counterexample (rhsName <> " = " <> show rhs) $
      eqE lhs rhs

rbindE :: Distinct o => Scope o -> F.Expr i -> (Name i -> F.Expr o) -> F.Expr o
rbindE = rbind

rreturnE :: Name n -> F.Expr n
rreturnE = rreturn

liftRME :: Distinct o => Scope o -> (Name i -> Name o) -> F.Expr i -> F.Expr o
liftRME = liftRM

-- | Run a law on terms.
onTerms :: Verdict -> String -> (forall n. Ctx n -> F.Expr n -> Property) -> Spec
onTerms verdict name p = law verdict name $
  forAllShrinkShow (genTermCase sg) shrinkTermCase (showTermCase sg) $ \(TermCase n t) ->
    p n (fromAST t)

-- | Run a law on renamings of each class.
onRenamings
  :: (RenamingClass -> Verdict) -> String
  -> (forall n. Chain' n -> F.Expr n -> Property) -> Spec
onRenamings verdict name p = forM_ allRenamingClasses $ \cls ->
  describe ("along " <> show cls) $ law (verdict cls) name $
    forAllShrinkShow (genRenamingCase sg cls) shrinkRenamingCase (showRenamingCase sg) $
      \(RenamingCase chain t) -> p chain (fromAST t)

-- | Run a law on substitutions of each pair of kinds.
onSubsts
  :: String
  -> (forall i o1 o2. (Distinct o1, Distinct o2)
        => Ctx i -> Scope o1 -> Scope o2
        -> Substitution F.Expr i o1 -> Substitution F.Expr o1 o2
        -> F.Expr i -> Property)
  -> Spec
onSubsts name p = describe name $
  forM_ [ (k1, k2) | k1 <- [minBound .. maxBound], k2 <- [minBound .. maxBound] ] $ \(k1, k2) ->
    law Holds ("s1 " <> show k1 <> ", s2 " <> show k2) $
      forAllShrinkShow (genSubstCase sg k1 k2) shrinkSubstCase (showSubstCase sg) $
        \(SubstCase i o1 o2 s1 s2 t) -> withCtx o1 $ \scope1 -> withCtx o2 $ \scope2 ->
          p i scope1 scope2
            (mapSubst fromAST (substValue s1)) (mapSubst fromAST (substValue s2)) (fromAST t)

-- | The identity substitution with every name mapped explicitly.
explicitIdentity :: Ctx n -> Substitution F.Expr n n
explicitIdentity n =
  nameMapToSubstitution (addNameBinderList (ctxChain n) (map F.VarE (ctxNames n)) emptyNameMap)

spec :: Spec
spec = do
  describe "Sinkable (hand-written, through extendRenaming)" $
    sinkableSpec (const eqE) show
      (\ctx -> fromAST <$> sized (genAST sg ctx . min 30))
      (map fromAST . shrinkAST . toAST)
      (\_ _ -> Holds)

  describe "liftRM (through rbind)" $ do
    onTerms Holds "liftRM n id t ≡α t" $ \n t -> withCtx n $ \scope ->
      cmp "liftRM n id t" (liftRME scope id t) "t" t
    onRenamings (const Holds) "liftRM k (g . f) t ≡α liftRM k g (liftRM l f t)" $
      \(Chain' _ l k f g _) t -> withCtx l $ \scopeL -> withCtx k $ \scopeK ->
        cmp "liftRM k (g . f) t" (liftRME scopeK (rename g . rename f) t)
            "liftRM k g (liftRM l f t)" (liftRME scopeK (rename g) (liftRME scopeL (rename f) t))

  describe "sinkabilityProof and liftRM" $
    onRenamings
      (\case
        Inclusions -> Holds
        _ -> KnownFailure "extendRenaming is a coercion, so free names under a binder are not renamed")
      "sinkabilityProof f t ≡α liftRM l f t" $
      \(Chain' _ l _ f _ _) t -> withCtx l $ \scopeL ->
        cmp "sinkabilityProof f t" (sinkabilityProof (rename f) t)
            "liftRM l f t" (liftRME scopeL (rename f) t)

  describe "substitute" $ do
    onSubsts "left unit" $ \i scope1 _ s1 _ _ ->
      conjoin [ cmp "substitute o1 s1 (VarE x)" (F.substitute scope1 s1 (F.VarE x))
                    "lookupSubst s1 x" (lookupSubst s1 x)
              | x <- ctxNames i ]
    onTerms Holds "right unit" $ \n t -> withCtx n $ \scope ->
      cmp "substitute n identitySubst t" (F.substitute scope identitySubst t) "t" t
    onTerms Holds "right unit (explicit identity)" $ \n t -> withCtx n $ \scope ->
      cmp "substitute n (explicit identity) t" (F.substitute scope (explicitIdentity n) t) "t" t
    onSubsts "associativity" $ \i scope1 scope2 s1 s2 t ->
      let composite = nameMapToSubstitution $ addNameBinderList (ctxChain i)
            [ F.substitute scope2 s2 (lookupSubst s1 x) | x <- ctxNames i ] emptyNameMap
       in cmp "substitute o2 s2 (substitute o1 s1 t)" (F.substitute scope2 s2 (F.substitute scope1 s1 t))
              "substitute o2 (s2 ⊙ s1) t" (F.substitute scope2 composite t)

  describe "rbind" $ do
    onTerms Holds "right unit" $ \n t -> withCtx n $ \scope ->
      cmp "rbind n t rreturn" (rbindE scope t rreturnE) "t" t
    onSubsts "associativity" $ \_ scope1 scope2 s1 s2 t ->
      let f = lookupSubst s1
          g = lookupSubst s2
       in cmp "rbind o2 (rbind o1 t f) g" (rbindE scope2 (rbindE scope1 t f) g)
              "rbind o2 t (\\x -> rbind o2 (f x) g)" (rbindE scope2 t (\x -> rbindE scope2 (f x) g))
    onSubsts "agrees with substitute" $ \_ scope1 _ s1 _ t ->
      cmp "substitute o1 s1 t" (F.substitute scope1 s1 t)
          "rbind o1 t (lookupSubst s1)" (rbindE scope1 t (lookupSubst s1))
