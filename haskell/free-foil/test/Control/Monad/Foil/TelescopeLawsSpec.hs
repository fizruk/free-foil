{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The laws of "Control.Monad.Foil.Laws" for telescopes, and one law that
-- only patterns with payloads have: refreshing a telescope transports its
-- payloads along the refreshed binders ('Foil.PatternTransport'). Payloads
-- are names or terms of the λ-calculus of "Control.Monad.Free.Foil.Example".
module Control.Monad.Foil.TelescopeLawsSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Foil
import           Control.Monad.Foil.Internal           (Name (..))
import           Control.Monad.Foil.Laws
import           Control.Monad.Foil.Relative           (RelMonad)
import           Control.Monad.Foil.Telescope          (Telescope (..))
import           Control.Monad.Free.Foil               (AST (..), substitute)
import           Control.Monad.Free.Foil.Example       (Expr, ExprF, pattern AppE, pattern LamE)
import           Control.Monad.Free.Foil.ExampleSyntax (exprSyntax)
import           Control.Monad.Free.Foil.Laws

-- | Telescopes of up to three steps, with payloads from a generator. The
-- telescope stops early where there is no payload to give.
genTelescope :: forall e. (forall n. Ctx n -> Gen (Maybe (e n))) -> GenPattern (Telescope () e)
genTelescope genE ctx0 = do
  k <- chooseInt (0, 3)
  go k ctx0
  where
    go :: Int -> Ctx n -> Gen (PatIn (Telescope () e) n)
    go k ctx = withCtx ctx $ \scope ->
      if k <= 0
        then pure (PatIn TelescopeEmpty)
        else genE ctx >>= \case
          Nothing -> pure (PatIn TelescopeEmpty)
          Just payload ->
            withHintedBinder scope $ \binder -> do
              PatIn rest <- go (k - 1) (extendCtx ctx binder)
              pure (PatIn (TelescopeCons () payload binder rest))

-- | The binders of a telescope, in order.
telescopeNames :: PatternNames (Telescope label e)
telescopeNames = \case
  TelescopeEmpty              -> []
  TelescopeCons _ _ b rest    -> nameId (nameOf b) : telescopeNames rest

-- | Payloads that are names of the scope before the step, if it has any.
genNamePayload :: Ctx n -> Gen (Maybe (Name n))
genNamePayload ctx = case ctxNames ctx of
  [] -> pure Nothing
  xs -> Just <$> elements xs

sg :: SyntaxGen NameBinder ExprF
sg = exprSyntax genNameBinder nameBinderNames

-- | Payloads that are λ-terms.
genTermPayload :: Ctx n -> Gen (Maybe (Expr n))
genTermPayload ctx = Just <$> sized (genAST sg ctx . min 8)

-- | A telescope with a body, as one λ-term: each step @(x : A)@ becomes
-- @A (λx. …)@, so that α-equivalence of the encodings is α-equivalence of
-- the telescopes with their bodies.
encode :: (forall x. e x -> Expr x) -> Telescope () e n l -> Expr l -> Expr n
encode f = \case
  TelescopeEmpty -> id
  TelescopeCons () payload binder rest -> \body ->
    AppE (f payload) (LamE binder (encode f rest body))

-- | A telescope with a body, decoded from its encoding.
data Decoded e n where
  Decoded :: Telescope () e n l -> Expr l -> Decoded e n

-- | Decode @k@ steps of an encoding.
decode :: (forall x. Expr x -> Maybe (e x)) -> Int -> Expr n -> Maybe (Decoded e n)
decode f k t
  | k <= 0 = Just (Decoded TelescopeEmpty t)
  | AppE a (LamE binder rest) <- t = do
      payload <- f a
      Decoded tele body <- decode f (k - 1) rest
      Just (Decoded (TelescopeCons () payload binder tele) body)
  | otherwise = Nothing

-- | Refreshing a telescope with 'withRefreshedPattern', and its body with
-- the substitution it returns, gives an α-variant. The telescope is built
-- in a scope @n@ and sunk (through its encoding) into an extension @o@ of
-- @n@ that binds the names of its binders, so that every binder clashes.
transportLaw
  :: (Sinkable e, RelMonad Name e)
  => (forall x. e x -> Expr x) -> (forall x. Expr x -> Maybe (e x))
  -> (forall x. Ctx x -> Gen (Maybe (e x)))
  -> Property
transportLaw toE fromE genE =
  forAllShow genCase showCase $ \(TransportCase o k enc) -> withCtx o $ \scopeO ->
    case decode fromE k enc of
      Nothing -> counterexample "the encoding does not decode" False
      Just (Decoded tele body) ->
        withRefreshedPattern scopeO tele $ \extend tele' scope' ->
          let body' = substitute scope' (extend identitySubst) body
              refreshed = encode toE tele' body'
           in counterexample ("refreshed = " <> showAST sg refreshed) $
                alphaEqNameless nameBinderNames enc refreshed
  where
    genCase = do
      SomeCtx n <- genCtx
      PatIn tele <- genTelescope genE n
      body <- sized (genAST sg (extendCtx n tele) . min 8)
      let names = telescopeNames tele
      withCtx n $ \scopeN ->
        clashWith names scopeN $ \o ->
          let enc = sink (encode toE tele body)
           in pure (TransportCase (extendCtx n o) (length names) enc)

    -- Extend a scope by binders with the given names, which are fresh for it.
    clashWith :: Distinct n => [Int] -> Scope n -> (forall o. DExt n o => NameBinderList n o -> r) -> r
    clashWith [] _ cont = cont NameBinderListEmpty
    clashWith (x : xs) scope cont = withRefreshed scope (UnsafeName x) $ \b ->
      clashWith xs (extendScope b scope) $ \bs -> cont (NameBinderListCons b bs)

    showCase (TransportCase o _ enc) = unlines [ "o = " <> showCtx o, "encoding = " <> showAST sg enc ]

-- | An encoded telescope of @k@ steps in a scope @o@.
data TransportCase where
  TransportCase :: Ctx o -> Int -> Expr o -> TransportCase

spec :: Spec
spec = do
  describe "Telescope () Name" $ do
    coSinkableSpec telescopeNames (genTelescope genNamePayload) extensionByCoercion
    law Holds "withRefreshedPattern transports payloads along refreshed binders" $
      transportLaw Var (\case Var x -> Just x; _ -> Nothing) genNamePayload
  describe "Telescope () Expr" $ do
    coSinkableSpec telescopeNames (genTelescope genTermPayload) extensionByCoercion
    law Holds "withRefreshedPattern transports payloads along refreshed binders" $
      transportLaw id Just genTermPayload
