{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE LambdaCase          #-}
-- @Ext VoidS n@ is simplifiable against the @Ext@ instance; this is what GHC
-- suggests instead of unfolding it by hand.
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Supports and scope restriction.
--
-- The foil accounts for scope extension, where 'Foil.sink' is a coercion.
-- Restriction is the other direction and cannot be: a term's support is
-- contained in its scope, and the converse has to be tested. These are the
-- properties of that test, and of the support it is made from.
--
-- The case worth reading is the last one. Raw names are not unique across scope
-- indices — 'Foil.sink' is a coercion and does not rename, so a term carried
-- into a larger scope keeps its binder names, and one of them may coincide with
-- a name already there. This is not a contrived configuration: it is what makes
-- 'Foil.withRefreshedPattern' unable to take an all-binders-already-fresh fast
-- path, and one \(\beta\)-step is enough to produce it. It is also why a support
-- has to drop binder names one binder at a time: dropping /all/ of a term's
-- binder names from /all/ of its variables at the end would be wrong.
module Control.Monad.Free.Foil.SupportSpec (spec) where

import           Data.Bifoldable
import           Data.Bifunctor
import           Test.Hspec

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil

-- | Untyped λ-calculus: the smallest signature with a binder in it.
data LamSig scope term
  = AppSig term term
  | LamSig scope
  deriving (Functor, Foldable, Traversable)

instance Bifunctor LamSig where
  bimap f g = \case
    AppSig fun arg -> AppSig (g fun) (g arg)
    LamSig body    -> LamSig (f body)

instance Bifoldable LamSig where
  bifoldMap f g = \case
    AppSig fun arg -> g fun <> g arg
    LamSig body    -> f body

type Lam = AST Foil.NameBinder LamSig

var :: Foil.Name n -> Lam n
var = Var

app :: Lam n -> Lam n -> Lam n
app fun arg = Node (AppSig fun arg)

-- | @λ x. body x@, with a binder fresh in the given scope.
lam
  :: Foil.Distinct n
  => Foil.Scope n
  -> (forall l. Foil.DExt n l => Foil.Scope l -> Foil.Name l -> Lam l)
  -> Lam n
lam scope body = Foil.withFresh scope $ \binder ->
  Node (LamSig (ScopedAST binder
    (body (Foil.extendScope binder scope) (Foil.nameOf binder))))

-- | One \(\beta\)-step at the head, via the library's own substitution.
beta :: Foil.Distinct n => Foil.Scope n -> Lam n -> Lam n
beta scope = \case
  Node (AppSig (Node (LamSig (ScopedAST binder body))) arg) ->
    substitute scope (Foil.addSubst Foil.identitySubst binder arg) body
  term -> term

-- | Work in a scope holding one name.
withOne
  :: (forall n. Foil.DExt Foil.VoidS n => Foil.Scope n -> Foil.Name n -> r) -> r
withOne k = Foil.withFresh Foil.emptyScope $ \binder ->
  k (Foil.extendScope binder Foil.emptyScope) (Foil.nameOf binder)

-- | Work in a scope holding two names.
withTwo
  :: (forall n. Foil.DExt Foil.VoidS n
      => Foil.Scope n -> Foil.Name n -> Foil.Name n -> r)
  -> r
withTwo k = Foil.withFresh Foil.emptyScope $ \b0 ->
  let scope0 = Foil.extendScope b0 Foil.emptyScope
   in Foil.withFresh scope0 $ \b1 ->
        k (Foil.extendScope b1 scope0)
          (Foil.sink (Foil.nameOf b0))
          (Foil.nameOf b1)

-- | The raw identifiers of a term's support, which is what the assertions
-- compare.
support :: Foil.Distinct n => Lam n -> [Int]
support = map Foil.nameId . freeVarsOf

-- | The raw identifiers a term binds, so that the shadowing case below can
-- assert that it really is one.
binderIds :: Lam n -> [Int]
binderIds = \case
  Var _     -> []
  Node node -> bifoldMap
    (\(ScopedAST binder body) ->
      Foil.nameId (Foil.nameOf binder) : binderIds body)
    binderIds
    node

spec :: Spec
spec = do
  describe "supportOf" $ do
    it "is empty for a closed term" $
      support (lam Foil.emptyScope (\_ x -> var x)) `shouldBe` []

    it "is the variable itself for a free variable" $
      withOne (\_ x -> support (var x)) `shouldBe` [0]

    it "drops what a binder binds and keeps what it does not" $
      withOne (\scope x ->
        support (lam scope (\_ y -> app (var (Foil.sink x)) (var y))))
        `shouldBe` [0]

    it "reports each free variable once, in ascending order" $
      withTwo (\_ x y -> support (app (app (var y) (var x)) (var y)))
        `shouldBe` [0, 1]

  describe "unsinkAST" $ do
    it "restricts a term that does not use what was dropped" $
      withOne (\scope _ ->
        fmap support (unsinkAST Foil.emptyScope (lam scope (\_ y -> var y))))
        `shouldBe` Just []

    it "refuses a term that does use it" $
      withOne (\_ x ->
        case unsinkAST Foil.emptyScope (var x) of
          Nothing                    -> True
          Just (_ :: Lam Foil.VoidS) -> False)
        `shouldBe` True

  describe "withRelevantScope" $
    it "always succeeds, and keeps exactly the support" $
      withTwo (\scope x y ->
        let term = app (var y) (lam scope (\_ z -> var z))
         in withRelevantScope term $ \relevant term' ->
              ( Foil.nameSetSize (Foil.scopeToNameSet relevant)
              , support term'
              , Foil.member x relevant ))
        `shouldBe` (1, [1], False)

  describe "a binder sharing a raw name with the enclosing scope" $
    it "does not remove the enclosing name from the support" $
      -- Reducing `(λ g. g x) two`, where `two = λ s. λ z. s z` was built
      -- elsewhere and so binds raw name 0, places that binder in a scope where
      -- 0 is already the free variable `x`. The result, `two x`, must still
      -- have support {0}: the binder shadows nothing, because inside it raw 0
      -- denotes the bound variable. Removing every binder name from every
      -- variable would wrongly give an empty support here. The second
      -- component asserts that the reduct does bind raw 0, so that the case
      -- cannot quietly stop being the one it claims to be.
      withOne (\scope x ->
        let two = lam Foil.emptyScope (\scope' s ->
                    lam scope' (\_ z -> app (var (Foil.sink s)) (var z)))
            redex = app (lam scope (\_ g -> app (var g) (var (Foil.sink x))))
                        (Foil.sink two)
            reduct = beta scope redex
         in (support reduct, binderIds reduct))
        `shouldBe` ([0], [0, 1])
