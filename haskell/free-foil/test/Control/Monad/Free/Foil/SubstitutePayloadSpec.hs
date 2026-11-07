{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | A substitution reaches the payloads of binders.
--
-- The binder here carries a term, the type of its name, in the scope before
-- it, as a typed λ does: @λ(x : A). b@. Substituting for a name the payload
-- mentions has to change the payload, as it changes the body. Up to 0.6.1
-- 'substitute' entered binders with 'Foil.withRefreshedPattern', which moves
-- a payload along the binders alone, so the payload kept the substituted
-- name.
--
-- The names a payload uses are free in the term, as those of its body are.
-- Up to 0.6.1 'supportOf' took the support of a scoped term from its body
-- alone, so the restriction of a term could drop a name only a payload uses.
module Control.Monad.Free.Foil.SubstitutePayloadSpec (spec) where

import           Test.Hspec

import           Data.Bifoldable                 (Bifoldable (..))

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Foil.Relative     (RelMonad (..))
import           Control.Monad.Foil.Telescope    (Telescope (..), telescopePayloads)
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.Example (ExprF (..), pattern AppE, pattern LamE)

-- | A binder with the type of its name.
data Typed (n :: Foil.S) (l :: Foil.S) where
  Typed :: Term n -> Foil.NameBinder n l -> Typed n l

-- | Terms whose λ binds a typed name.
type Term = AST Typed ExprF

-- | A variable as a term.
var :: Foil.Name n -> Term n
var = Var

-- | The example signature derives 'Data.Bifunctor.Bifunctor' only, and
-- 'freeVarsOf' folds.
instance Bifoldable ExprF where
  bifoldMap _ g (AppF f a) = g f <> g a
  bifoldMap f _ (LamF body) = f body

instance Foil.CoSinkable Typed where
  coSinkabilityProof rename (Typed ty x) cont =
    Foil.coSinkabilityProof rename x $ \rename' x' -> cont rename' (Typed (Foil.sinkabilityProof rename ty) x')

  withPattern
    :: forall f o n l r. Foil.Distinct o
    => (forall x y z r'. Foil.Distinct z
          => Foil.Scope z
          -> Foil.NameBinder x y
          -> (forall z'. Foil.DExt z z' => f x y z z' -> Foil.NameBinder z z' -> r')
          -> r')
    -> (forall x z z'. Foil.DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (Foil.DExt z z', Foil.DExt z' z'')
          => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Foil.Scope o
    -> Typed n l
    -> (forall o'. Foil.DExt o o' => f n l o o' -> Typed o o' -> Foil.Scope o' -> r)
    -> r
  withPattern withBinder _ _ scope (Typed ty x) cont =
    withBinder scope x $ \fx x' ->
      cont fx (Typed (Foil.transportPayload scope Foil.verbatimTransport ty) x') (Foil.extendScope x' scope)

  type Payload Typed = Term

  withMappedPattern refresh extend _ mapPayload scope m (Typed ty x) cont =
    refresh scope x $ \x' ->
      cont (extend m x x') (Typed (mapPayload scope m ty) x') (Foil.extendScope x' scope)

  foldMapPayloads f (Typed ty _) = f ty

instance Foil.SinkableK Typed where
  sinkabilityProofK = Foil.sinkabilityProofKViaCoSinkable

-- | The payload of the outermost binder of a term.
payloadOf :: Term n -> Maybe String
payloadOf = \case
  LamE (Typed ty _) _ -> Just (render ty)
  _ -> Nothing

-- | A term with its raw names, enough to tell which name a payload holds.
render :: Term n -> String
render = \case
  Var x -> "x" ++ show (Foil.nameId x)
  AppE f a -> "(" ++ render f ++ " " ++ render a ++ ")"
  LamE (Typed ty x) body -> "\\(x" ++ show (Foil.nameId (Foil.nameOf x)) ++ " : " ++ render ty ++ "). " ++ render body

-- | The term @λ(x : a). x@ in the scope of @a@, and the substitution of @b@
-- for @a@ into the scope of @a@ and @b@. The binder @x@ is fresh for @a@
-- alone, so it clashes with @b@ and is refreshed as well.
withExample
  :: (forall i n l. (Foil.Distinct i, Foil.Distinct n) => Foil.Scope n -> Foil.Name n -> Term i -> Telescope () Term i l -> Foil.Substitution Term i n -> r)
  -> r
withExample k =
  Foil.withFresh Foil.emptyScope $ \a ->
    let scopeA = Foil.extendScope a Foil.emptyScope
    in Foil.withFresh scopeA $ \b ->
      let scope = Foil.extendScope b scopeA
      in Foil.withFresh scopeA $ \x ->
        let term = LamE (Typed (Var (Foil.nameOf a)) x) (Var (Foil.nameOf x))
            tele = TelescopeCons () (Var (Foil.nameOf a)) x TelescopeEmpty
            subst = Foil.addSubst (Foil.sink Foil.identitySubst) a (Var (Foil.nameOf b))
        in k scope (Foil.nameOf b) term tele subst

spec :: Spec
spec = describe "a substitution reaches the payloads of binders" $ do
  it "substitute" $
    withExample $ \scope b term _ subst ->
      payloadOf (substitute scope subst term) `shouldBe` Just (render (Var b))
  it "substituteRefreshed" $
    withExample $ \scope b term _ subst ->
      payloadOf (substituteRefreshed scope subst term) `shouldBe` Just (render (Var b))
  it "rbind" $
    withExample $ \scope b term _ subst ->
      payloadOf (rbind scope term (Foil.lookupSubst subst)) `shouldBe` Just (render (Var b))
  it "the payloads of a telescope" $
    withExample $ \scope b _ tele subst ->
      Foil.withSubstitutedPattern Foil.substitutePayload scope subst tele $ \_ tele' _ ->
        map render (telescopePayloads tele') `shouldBe` [render (Var b)]

  describe "the support of a term includes the payloads of its binders" $ do
    it "freeVarsOf" $
      Foil.withFresh Foil.emptyScope $ \a ->
        let scope = Foil.extendScope a Foil.emptyScope
        in Foil.withFresh scope $ \x ->
          map Foil.nameId (freeVarsOf (LamE (Typed (Var (Foil.nameOf a)) x) (Var (Foil.nameOf x))))
            `shouldBe` [Foil.nameId (Foil.nameOf a)]
    it "freeVarsOf, a payload naming an outer binder" $
      Foil.withFresh Foil.emptyScope $ \a ->
        let scopeA = Foil.extendScope a Foil.emptyScope
        in Foil.withFresh scopeA $ \x ->
          Foil.withFresh (Foil.extendScope x scopeA) $ \y ->
            map Foil.nameId (freeVarsOf (LamE (Typed (Var (Foil.nameOf a)) x) (LamE (Typed (Var (Foil.nameOf x)) y) (Var (Foil.nameOf y)))))
              `shouldBe` [Foil.nameId (Foil.nameOf a)]
    it "unsinkAST keeps a name only a payload uses" $
      Foil.withFresh Foil.emptyScope $ \a ->
        let scope = Foil.extendScope a Foil.emptyScope
        in Foil.withFresh scope $ \x ->
          fmap render (unsinkAST Foil.emptyScope (LamE (Typed (Var (Foil.nameOf a)) x) (Var (Foil.nameOf x))))
            `shouldBe` Nothing
    it "the payloads of a telescope, its own names removed" $
      Foil.withFresh Foil.emptyScope $ \a ->
        let scopeA = Foil.extendScope a Foil.emptyScope
        in Foil.withFresh scopeA $ \x ->
          Foil.withFresh (Foil.extendScope x scopeA) $ \y ->
            let tele = TelescopeCons () (var (Foil.nameOf a)) x (TelescopeCons () (var (Foil.nameOf x)) y TelescopeEmpty)
            in map Foil.nameId (Foil.nameSetToList (Foil.unsinkNameSet tele (Foil.payloadsSupport tele)))
                 `shouldBe` [Foil.nameId (Foil.nameOf a)]
