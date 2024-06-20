{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
-- | Free foil implementation of the \(\lambda\Pi\)-calculus (with pairs).
--
-- Free foil provides __general__ definitions or implementations for the following:
--
-- 1. Freely generated (from a simple signature) scope-safe AST.
-- 2. Correct capture-avoiding substitution (see 'substitute').
-- 3. Correct α-equivalence checks (see 'alphaEquiv' and 'alphaEquivRefreshed') as well as α-normalization (see 'refreshAST').
-- 4. Conversion helpers (see 'convertToAST' and 'convertFromAST').
--
-- The following is __generated__ using Template Haskell:
--
-- 1. Convenient pattern synonyms.
-- 2. 'ZipMatch' instances (enabling general α-equivalence).
-- 3. Conversion between scope-safe and raw term representation.
--
-- The following is implemented __manually__ in this module:
--
-- 1. Computation of weak head normal form (WHNF), see 'whnf'.
-- 2. Entry point, gluing everything together. See 'defaultMain'.
--
-- __Note:__ free foil does not (easily) support patterns at the moment,
-- so only wildcard patterns and variable patterns are handled in this implementation.
module Language.LambdaPi.Impl.FreeFoilTH where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Free.Foil
import           Control.Monad.Free.Foil.TH
import           Data.Bifunctor.TH
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.String                     (IsString (..))
import qualified Language.LambdaPi.Syntax.Abs    as Raw
import qualified Language.LambdaPi.Syntax.Layout as Raw
import qualified Language.LambdaPi.Syntax.Lex    as Raw
import qualified Language.LambdaPi.Syntax.Par    as Raw
import qualified Language.LambdaPi.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> import Control.Monad.Free.Foil
-- >>> import Data.String (fromString)

-- * Generated code

-- ** Signature
mkSignature ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
deriveZipMatch ''Term'Sig
deriveBifunctor ''Term'Sig
deriveBifoldable ''Term'Sig
deriveBitraversable ''Term'Sig

-- ** Pattern synonyms
mkPatternSynonyms ''Term'Sig

-- ** Conversion helpers

mkConvertToFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'
mkConvertFromFreeFoil ''Raw.Term' ''Raw.VarIdent ''Raw.ScopedTerm' ''Raw.Pattern'

-- * User-defined code

type Term' a = AST (Term'Sig a)
type Term = Term' Raw.BNFC'Position

-- ** Conversion helpers

-- | Convert 'Raw.Term'' into a scope-safe term.
-- This is a special case of 'convertToAST'.
toTerm' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> AST (Term'Sig a) n
toTerm' = convertToAST convertToTerm'Sig getPattern'Binder getTerm'FromScopedTerm'

-- | Convert 'Raw.Term'' into a closed scope-safe term.
-- This is a special case of 'toTerm''.
toTerm'Closed :: Raw.Term' a -> AST (Term'Sig a) Foil.VoidS
toTerm'Closed = toTerm' Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'Raw.Term''.
-- This is a special case of 'convertFromAST'.
--
-- 'Raw.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromTerm' :: AST (Term'Sig a) n -> Raw.Term' a
fromTerm' = convertFromAST
  convertFromTerm'Sig
  (Raw.Var (error "location missing"))
  (Raw.PatternVar (error "location missing"))
  (Raw.AScopedTerm (error "location missing"))
  (\n -> Raw.VarIdent ("x" ++ show n))

-- | Parse scope-safe terms via raw representation.
--
-- >>> fromString "λx.λy.λx.x" :: Term Foil.VoidS
-- λ x0 . λ x1 . λ x2 . x2
instance IsString (AST (Term'Sig Raw.BNFC'Position) Foil.VoidS) where
  fromString input = case Raw.pTerm (Raw.tokens input) of
    Left err   -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
    Right term -> toTerm'Closed term

-- | Pretty-print scope-safe terms via raw representation.
instance Show (AST (Term'Sig a) Foil.VoidS) where
  show = Raw.printTree . fromTerm'

-- ** Evaluation

-- | Compute weak head normal form (WHNF) of a λΠ-term.
--
-- >>> whnf Foil.emptyScope "(λx.(λ_.x)(λy.x))(λy.λz.z)"
-- λ x0 . λ x1 . x1
--
-- >>> whnf Foil.emptyScope "(λs.λz.s(s(z)))(λs.λz.s(s(z)))"
-- λ x1 . (λ x0 . λ x1 . x0 (x0 x1)) ((λ x0 . λ x1 . x0 (x0 x1)) x1)
--
-- Note that during computation bound variables can become unordered
-- in the sense that binders may easily repeat or decrease. For example,
-- in the following expression, inner binder has lower index that the outer one:
--
-- >>> whnf Foil.emptyScope "(λx.λy.x)(λx.x)"
-- λ x1 . λ x0 . x0
--
-- At the same time, without substitution, we get regular, increasing binder indices:
--
-- >>> "λx.λy.y" :: Term Foil.VoidS
-- λ x0 . λ x1 . x1
--
-- To compare terms for \(\alpha\)-equivalence, we may use 'alphaEquiv':
--
-- >>> alphaEquiv Foil.emptyScope (whnf Foil.emptyScope "(λx.λy.x)(λx.x)") "λx.λy.y"
-- True
--
-- We may also normalize binders using 'refreshAST':
--
-- >>> refreshAST Foil.emptyScope (whnf Foil.emptyScope "(λx.λy.x)(λx.x)")
-- λ x0 . λ x1 . x1
whnf :: Foil.Distinct n => Foil.Scope n -> Term n -> Term n
whnf scope = \case
  App loc f x ->
    case whnf scope f of
      Lam _loc binder body ->
        let subst = Foil.addSubst Foil.identitySubst binder x
         in whnf scope (substitute scope subst body)
      f' -> App loc f' x
  First loc t ->
    case whnf scope t of
      Pair _loc l _r -> whnf scope l
      t'             -> First loc t'
  Second loc t ->
    case whnf scope t of
      Pair _loc _l r -> whnf scope r
      t'             -> Second loc t'
  t -> t

-- ** Type checking


-- ** λΠ-interpreter

-- | Interpret a λΠ command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute _loc term _type) =
      putStrLn ("  ↦ " ++ show (whnf Foil.emptyScope (toTerm'Closed term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _loc _term _type) = putStrLn "check is not yet implemented"

-- | Interpret a λΠ program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram _loc typedTerms) = mapM_ interpretCommand typedTerms

-- | A λΠ interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pProgram (Raw.resolveLayout True (Raw.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
