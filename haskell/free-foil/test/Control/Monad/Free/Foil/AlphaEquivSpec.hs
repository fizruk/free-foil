{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

-- | Properties of 'alphaEquiv' with threaded renamings.
--
-- Two soundness surfaces are pinned here. The rename path must stay
-- /linear/: a chain of binders that mismatch at every level (the shifted
-- chain below) used to make the eager implementation rename the whole
-- remaining body per level. And the environments must not conflate a
-- renamed bound name with a name that passes through unchanged and
-- happens to share the spelling; the hand-built terms below are exactly
-- the conflations a raw-name-target environment would commit.
module Control.Monad.Free.Foil.AlphaEquivSpec (spec) where

import           Data.Bifunctor.TH
import           Data.Maybe                  (fromMaybe)
import           Test.Hspec
import           Test.Hspec.QuickCheck       (prop)
import           Test.QuickCheck

import qualified Control.Monad.Foil          as Foil
import           Control.Monad.Foil.Internal (Name (..), NameBinder (..),
                                              unsafeAssertFresh)
import           Control.Monad.Free.Foil
import           Data.ZipMatchK.TH           (deriveZipMatchK)
import           Generics.Kind.TH            (deriveGenericK)

data LamSig scope term
  = App term term
  | Lam scope
  deriving (Functor, Foldable, Traversable)

deriveBifunctor ''LamSig
deriveBifoldable ''LamSig
deriveBitraversable ''LamSig
deriveZipMatchK ''LamSig

type Term = AST Foil.NameBinder LamSig

-- | A binder annotated with a name of the outer scope, as a binder may be
-- annotated with its type. Only 'Foil.unifyPatternsIn' compares the
-- annotations, as it does the payloads of a telescope.
data AnnBinder (n :: Foil.S) (l :: Foil.S) where
  AnnBinder :: Foil.Name n -> Foil.NameBinder n l -> AnnBinder n l

deriveGenericK ''AnnBinder
instance Foil.SinkableK AnnBinder

-- | The annotation is a payload, so it is moved by hand (see
-- 'Foil.transportPayload').
instance Foil.CoSinkable AnnBinder where
  coSinkabilityProof rename (AnnBinder ann binder) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      cont rename' (AnnBinder (rename ann) binder')
  withPattern withBinder _unit _comp scope (AnnBinder ann binder) cont =
    withBinder scope binder $ \fbinder binder' ->
      cont fbinder
        (AnnBinder (Foil.transportName Foil.verbatimTransport ann) binder')
        (Foil.extendScope binder' scope)
instance Foil.UnifiablePattern AnnBinder where
  unifyPatternsIn _scope l@(AnnBinder x _) r@(AnnBinder y _)
    | x == y    = Foil.unifyPatterns l r
    | otherwise = Foil.NotUnifiable

type AnnTerm = AST AnnBinder LamSig

-- | λ(x : ann). x
annId :: Foil.Distinct n => Foil.Scope n -> Foil.Name n -> AnnTerm n
annId scope ann = Foil.withFresh scope $ \x ->
  Node (Lam (ScopedAST (AnnBinder ann x) (Var (Foil.nameOf x))))

-- | Run a continuation in a scope with two names.
withTwoNames
  :: (forall n. Foil.Distinct n => Foil.Scope n -> Foil.Name n -> Foil.Name n -> r)
  -> r
withTwoNames cont =
  Foil.withFresh Foil.emptyScope $ \a ->
    let scope1 = Foil.extendScope a Foil.emptyScope
     in Foil.withFresh scope1 $ \b ->
          cont (Foil.extendScope b scope1) (Foil.sink (Foil.nameOf a)) (Foil.nameOf b)

-- * Hand-built terms with chosen binder names

-- | A binder with a chosen raw name — either fresh for the scope, or
-- deliberately equal to an enclosing binder's, which a term is allowed to
-- carry (shadowing) and which the comparison must handle.
lam :: Int -> (forall l. Foil.DExt n l => Foil.Name l -> Term l) -> Term n
lam raw mkBody =
  unsafeAssertFresh (UnsafeNameBinder (UnsafeName raw)) $ \binder ->
    Node (Lam (ScopedAST binder (mkBody (Foil.nameOf binder))))

app :: Term n -> Term n -> Term n
app f x = Node (App f x)

-- * The shifted chain (the quadratic-rename regression)

-- | λx1. λx2. … λxn. xn, allocated in the given scope.
chainIn :: Foil.Distinct n => Foil.Scope n -> Int -> Foil.Name n -> Term n
chainIn _scope 0 x = Var x
chainIn scope k _x = Foil.withFresh scope $ \binder ->
  let scope' = Foil.extendScope binder scope
   in Node (Lam (ScopedAST binder (chainIn scope' (k - 1) (Foil.nameOf binder))))

-- | The chain over the empty scope: binders 0, 1, …, n−1.
plainChain :: Int -> Term Foil.VoidS
plainChain n = Foil.withFresh Foil.emptyScope $ \b0 ->
  let scope0 = Foil.extendScope b0 Foil.emptyScope
   in Node (Lam (ScopedAST b0 (chainIn scope0 (n - 1) (Foil.nameOf b0))))

-- | The same chain built under one dummy binder and cut back down:
-- binders 1, 2, …, n, so every level differs from 'plainChain' by one.
shiftedChain :: Int -> Term Foil.VoidS
shiftedChain n = Foil.withFresh Foil.emptyScope $ \dummy ->
  let scope1 = Foil.extendScope dummy Foil.emptyScope
      t = Foil.withFresh scope1 $ \b1 ->
            let scope2 = Foil.extendScope b1 scope1
             in Node (Lam (ScopedAST b1 (chainIn scope2 (n - 1) (Foil.nameOf b1))))
   in fromMaybe (error "the chain uses the dummy binder")
        (unsinkAST Foil.emptyScope t)

-- * Random terms, via a scope-free skeleton

-- | A closed λ-term skeleton: de Bruijn indices, so one skeleton renders
-- at any choice of binder names.
data Skel = SVar Int | SApp Skel Skel | SLam Skel
  deriving (Show)

genSkel :: Int -> Int -> Gen Skel
genSkel depth size
  | size <= 1 && depth > 0 = SVar <$> chooseInt (0, depth - 1)
  | otherwise = oneof $ concat
      [ [ SVar <$> chooseInt (0, depth - 1) | depth > 0 ]
      , [ SApp <$> genSkel depth (size `div` 2) <*> genSkel depth (size `div` 2) ]
      , [ SLam <$> genSkel (depth + 1) (size - 1) ]
      ]

instance Arbitrary Skel where
  arbitrary = sized (\s -> SLam <$> genSkel 1 s)

-- | Render a skeleton, allocating binder names with 'Foil.withFresh'.
renderIn :: Foil.Distinct n => Foil.Scope n -> [Foil.Name n] -> Skel -> Term n
renderIn scope env = \case
  SVar i      -> Var (env !! (i `mod` length env))
  SApp f x    -> app (renderIn scope env f) (renderIn scope env x)
  SLam body   -> Foil.withFresh scope $ \binder ->
    let scope' = Foil.extendScope binder scope
     in Node (Lam (ScopedAST binder
          (renderIn scope' (Foil.nameOf binder : map Foil.sink env) body)))

-- | Render over the empty scope; the top of every skeleton is a 'SLam',
-- so the environment is never consulted empty.
render :: Skel -> Term Foil.VoidS
render s = case s of
  SLam{} -> renderIn Foil.emptyScope [] s
  _      -> renderIn Foil.emptyScope [] (SLam s)

-- | Render under @k@ dummy binders and cut back down, so every binder
-- name shifts by @k@ and each level takes a rename branch.
renderShifted :: Int -> Skel -> Term Foil.VoidS
renderShifted k s = go k Foil.emptyScope
  where
    go :: (Foil.Distinct n, Foil.Ext Foil.VoidS n) => Int -> Foil.Scope n -> Term Foil.VoidS
    go 0 scope =
      fromMaybe (error "the term uses a dummy binder")
        (unsinkAST Foil.emptyScope (renderIn scope [] (case s of SLam{} -> s; _ -> SLam s)))
    go j scope = Foil.withFresh scope $ \dummy ->
      go (j - 1) (Foil.extendScope dummy scope)

spec :: Spec
spec = do
  describe "the rename path" $ do
    it "accepts the shifted chain (every binder differs)" $ do
      alphaEquiv Foil.emptyScope (plainChain 300) (shiftedChain 300)
        `shouldBe` True
    it "agrees with alphaEquivRefreshed on the shifted chain" $ do
      alphaEquivRefreshed Foil.emptyScope (plainChain 300) (shiftedChain 300)
        `shouldBe` True

  describe "no conflation of renamed and passthrough names" $ do
    -- λ7. λ5. (7,7) vs λ5. λ9. (5,9): a raw-name-target environment maps
    -- both sides to (5,5) and wrongly accepts; the terms differ.
    it "rejects λa.λb.(a,a) against λa.λb.(a,b) with adversarial names" $ do
      let t1 = lam 7 (\a -> lam 5 (\_b -> app (Var (Foil.sink a)) (Var (Foil.sink a))))
          t2 = lam 5 (\a -> lam 9 (\b -> app (Var (Foil.sink a)) (Var b)))
      alphaEquiv Foil.emptyScope t1 t2 `shouldBe` False
    it "accepts λa.λb.(a,b) against λa.λb.(a,b) with adversarial names" $ do
      let t1 = lam 7 (\a -> lam 5 (\b -> app (Var (Foil.sink a)) (Var b)))
          t2 = lam 5 (\a -> lam 9 (\b -> app (Var (Foil.sink a)) (Var b)))
      alphaEquiv Foil.emptyScope t1 t2 `shouldBe` True
    -- λ7. λ5. 7 vs λ5. λ5. 5: on the right the inner binder shadows the
    -- outer, so the bodies pick out different binders.
    it "rejects λa.λb.a against λa.λb.b when the right side shadows" $ do
      let t1 = lam 7 (\a -> lam 5 (\_b -> Var (Foil.sink a)))
          t2 = lam 5 (\_a -> lam 5 (\b -> Var b))
      alphaEquiv Foil.emptyScope t1 t2 `shouldBe` False
    it "accepts λa.λb.b against λa.λb.b when the right side shadows" $ do
      let t1 = lam 7 (\_a -> lam 5 (\b -> Var b))
          t2 = lam 5 (\_a -> lam 5 (\b -> Var b))
      alphaEquiv Foil.emptyScope t1 t2 `shouldBe` True

  describe "binders with annotations" $ do
    it "rejects λ(x : a). x against λ(x : b). x" $
      withTwoNames $ \scope a b ->
        alphaEquiv scope (annId scope a) (annId scope b) `shouldBe` False
    it "rejects λ(x : a). x against λ(x : b). x with alphaEquivRefreshed" $
      withTwoNames $ \scope a b ->
        alphaEquivRefreshed scope (annId scope a) (annId scope b) `shouldBe` False
    it "accepts λ(x : a). x against λ(y : a). y with alphaEquivRefreshed" $
      withTwoNames $ \scope a _ ->
        alphaEquivRefreshed scope (annId scope a) (annId scope a) `shouldBe` True

  describe "agreement with alphaEquivRefreshed" $ do
    prop "on a term against its shifted rendering" $ \s (Positive k) ->
      let t1 = render s
          t2 = renderShifted (k `mod` 5 + 1) s
       in alphaEquiv Foil.emptyScope t1 t2
            && alphaEquivRefreshed Foil.emptyScope t1 t2
    prop "on two independent terms" $ \s1 s2 ->
      let t1 = render s1
          t2 = render s2
       in alphaEquiv Foil.emptyScope t1 t2
            == alphaEquivRefreshed Foil.emptyScope t1 t2
    prop "on a term against a shifted different term" $ \s1 s2 (Positive k) ->
      let t1 = render s1
          t2 = renderShifted (k `mod` 5 + 1) s2
       in alphaEquiv Foil.emptyScope t1 t2
            == alphaEquivRefreshed Foil.emptyScope t1 t2
