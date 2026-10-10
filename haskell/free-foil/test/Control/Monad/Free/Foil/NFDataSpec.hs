{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
-- | 'rnf' of a term forces every field of every node, also the fields that
-- hold no subterms, which a traversal of the signature as a 'Bifoldable'
-- would skip.
module Control.Monad.Free.Foil.NFDataSpec (spec) where

import           Control.DeepSeq   (NFData, rnf)
import           Control.Exception (evaluate)
import           GHC.Generics      (Generic)
import           Test.Hspec

import qualified Control.Monad.Foil      as Foil
import           Control.Monad.Free.Foil

-- | λ-terms with integer literals.
data LitSig scope term
  = AppSig term term
  | LamSig scope
  | LitSig Int
  deriving (Generic, NFData)

type Term = AST Foil.NameBinder LitSig

-- | @λx. x lit@.
applyToLit :: Int -> Term Foil.VoidS
applyToLit n = Foil.withFresh Foil.emptyScope $ \binder ->
  Node (LamSig (ScopedAST binder (Node (AppSig (Var (Foil.nameOf binder)) (Node (LitSig n))))))

spec :: Spec
spec = describe "rnf of AST" $ do
  it "forces a term" $
    evaluate (rnf (applyToLit 1)) `shouldReturn` ()
  it "forces a field of the signature under a binder" $
    evaluate (rnf (applyToLit (error "the literal"))) `shouldThrow` errorCall "the literal"
