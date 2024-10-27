{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints -ddump-splices #-}
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
-- Lam (x0 . Lam (x2 . App (x2, App (App (x0, ?m [x0, x0]), x0))))
applySubsts :: Foil.Distinct n => Foil.Scope n -> [Subst] -> Term n -> Term n
applySubsts scope substs term =
  case term of
    MetaVar _loc m args | Just (Subst _ _ binders body) <- lookupSubst m substs ->
      substitutePattern scope Foil.voidSubst binders args body
    Var{} -> term
    Node node -> Node (bimap goScoped (applySubsts scope substs) node)
  where
    goScoped (ScopedAST binders body) =
      case Foil.assertDistinct binders of
        Foil.Distinct ->
          let scope' = Foil.extendScopePattern binders scope
           in ScopedAST binders (applySubsts scope' substs body)

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
