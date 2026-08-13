{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A record of sinkable fields is itself sinkable, with nothing written by
-- hand: 'deriveGenericK' plus empty 'SinkableK' and 'Sinkable' instances,
-- and the whole record then sinks in one coercion. This is the supported
-- alternative to a private @unsafeCoerce@ helper for environment records.
-- (A record holding the 'Scope' itself is refused — no @SinkableK Scope@ —
-- which is exactly the field such a helper would coerce unsoundly.)
module Control.Monad.Foil.SinkableSpec (spec) where

import           Data.Bifunctor.TH       (deriveBifunctor)
import qualified Data.Map                as Map
import           Generics.Kind.TH        (deriveGenericK)
import           Test.Hspec

import           Control.Monad.Foil
import           Control.Monad.Free.Foil (AST (Var))

-- | A miniature term type, enough for a table of terms in the record.
data ExprSig scope term = AppSig term term | LamSig scope
  deriving (Functor)
deriveBifunctor ''ExprSig

type Expr = AST NameBinder ExprSig

-- | The shape of a type checker's environment: scope-free fields next to
-- names, terms, tables, and pairs whose first component is scope-free.
data Env (n :: S) = Env
  { envDepth   :: Int
  , envNames   :: [Name n]
  , envTable   :: Map.Map String (Expr n)
  , envGoal    :: Maybe (Expr n, Expr n)
  , envSpelled :: [(String, Name n)]
  }

deriveGenericK ''Env

instance SinkableK Env
instance Sinkable Env

-- | 'sink', with the target scope pinned by a binder the caller holds.
sunkVia :: (Sinkable e, DExt n l) => NameBinder n l -> e n -> e l
sunkVia _ = sink

spec :: Spec
spec = describe "a record of sinkable fields" $
  it "derives Sinkable and sinks whole, contents untouched" $
    withFresh emptyScope $ \binder ->
      let x = nameOf binder
          env = Env 7 [x] (Map.singleton "f" (Var x)) (Just (Var x, Var x)) [("x", x)]
       in withFresh (extendScope binder emptyScope) $ \binder2 -> do
            let env' = sunkVia binder2 env   -- one coercion for the whole record
            envDepth env' `shouldBe` 7
            map nameId (envNames env') `shouldBe` [nameId x]
            Map.keys (envTable env') `shouldBe` ["f"]
            [nameId y | (_, y) <- envSpelled env'] `shouldBe` [nameId x]
            case envGoal env' of
              Just (Var a, Var b) -> (nameId a, nameId b) `shouldBe` (nameId x, nameId x)
              _                   -> expectationFailure "the goal lost its shape"
