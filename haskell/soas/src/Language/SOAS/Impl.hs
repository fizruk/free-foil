{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
-- | Functions over Second-Order Abstract Syntax (SOAS)
-- represented using scope-safe Haskell types (via Free Foil).
module Language.SOAS.Impl where


import Data.List (find)
import Data.Bifunctor
import qualified Control.Monad.Foil as Foil
import           Control.Monad.Free.Foil
import Language.SOAS.Impl.Generated
import qualified Language.SOAS.Syntax.Abs    as Raw
import qualified Language.SOAS.Syntax.Lex    as Raw
import qualified Language.SOAS.Syntax.Par    as Raw
import qualified Language.SOAS.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Standard Types

-- | Standard terms with source code location annotations.
type Term = Term' Raw.BNFC'Position
-- | Standard types with source code location annotations.
type Type = Type' Raw.BNFC'Position

-- | Standard metavariable substitutions with source code location annotations.
type Subst = Subst' Raw.BNFC'Position Foil.VoidS
-- | Standard unification constraints with source code location annotations.
type Constraint = Constraint' Raw.BNFC'Position Foil.VoidS
-- | Standard operator typings with source code location annotations.
type OpTyping = OpTyping' Raw.BNFC'Position Foil.VoidS

-- * Metavariable substitutions

-- | Lookup a substitution by its 'Raw.MetaVarIdent'.
--
-- >>> lookupSubst "?m" ["?n[] ↦ Zero()", "?m[x y] ↦ App(y, x)"]
-- Just ?m [x0 x1] ↦ App (x1, x0)
lookupSubst :: Raw.MetaVarIdent -> [Subst] -> Maybe Subst
lookupSubst m = find $ \(Subst _loc m' _ _) -> m == m'

-- | Apply meta variable substitutions to a term.
--
-- >>> applySubsts Foil.emptyScope ["?m[x y] ↦ Lam(z. App(z, App(x, y)))"] "Lam(x. ?m[App(x, ?m[x, x]), x])"
-- Lam (x0 . Lam (x2 . App (x2, App (App (x0, Lam (x2 . App (x2, App (x0, x0)))), x0))))
--
-- >>> applySubsts Foil.emptyScope ["?m[x y] ↦ App(y, x)"] "Lam(f. Lam(x. ?m[?m[x, f], f]))"
-- Lam (x0 . Lam (x1 . App (x0, App (x0, x1))))
applySubsts :: Foil.Distinct n => Foil.Scope n -> [Subst] -> Term n -> Term n
applySubsts scope substs term =
  case term of
    MetaVar _loc m args | Just (Subst _ _ binders body) <- lookupSubst m substs ->
      let args' = map (applySubsts scope substs) args
       in substitutePattern scope Foil.voidSubst binders args' body
    Var{} -> term
    -- NOTE: generic recursive processing!
    Node node -> Node (bimap goScoped (applySubsts scope substs) node)
  where
    goScoped (ScopedAST binders body) =
      case Foil.assertDistinct binders of
        Foil.Distinct ->
          let scope' = Foil.extendScopePattern binders scope
           in ScopedAST binders (applySubsts scope' substs body)

-- | Check if a (simultaneous) substitution is a solution to a set of constraints:
--
-- >>> isSolutionFor ["?m[x y] ↦ App(y, x)"] ["∀ f x. ?m[?m[x, f], f] = App(f, App(f, x))"]
-- True
-- >>> isSolutionFor ["?m[x y] ↦ App(y, x)"] ["∀ f x y. ?m[?m[x, f], f] = App(f, App(f, y))"]
-- False
--
-- >>> isSolutionFor ["?m[x] ↦ Lam(f. App(f, x))"] ["∀ x. ?m[?m[x]] = Lam(f. App(f, Lam(f. App(f, x))))"]
-- True
-- >>> isSolutionFor ["?m[x] ↦ Lam(f. App(f, x))"] ["∀ y x. ?m[?m[x]] = Lam(f. App(f, Lam(f. App(f, y))))"]
-- False
isSolutionFor :: [Subst] -> [Constraint] -> Bool
isSolutionFor substs = all isSatisfied
  where
    isSatisfied (ConstraintEq _loc binders l r) =
      case Foil.assertDistinct binders of
        Foil.Distinct ->
          let scope = Foil.extendScopePattern binders Foil.emptyScope
          in alphaEquiv scope (applySubsts scope substs l) (applySubsts scope substs r)

-- * Entrypoint

-- | A SOAS interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pTermTyping (Raw.tokens input) of
    Left err -> do
      putStrLn err
      exitFailure
    Right typing -> putStrLn (Raw.printTree typing)
