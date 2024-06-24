{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
-- | Free foil implementation of the \(\lambda\Pi\)-calculus (with pairs).
--
-- Free foil provides __general__ definitions or implementations for the following:
--
-- 1. Freely generated (from a simple signature) scope-safe AST.
-- 2. Correct capture-avoiding substitution (see 'substitute').
-- 3. Correct \(\alpha\)-equivalence checks (see 'alphaEquiv' and 'alphaEquivRefreshed') as well as \(\alpha\)-normalization (see 'refreshAST').
-- 4. Conversion helpers (see 'convertToAST' and 'convertFromAST').
--
-- The following is __generated__ using Template Haskell:
--
-- 1. Convenient pattern synonyms.
-- 2. 'ZipMatch' instances (enabling general \(\alpha\)-equivalence).
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
import           Control.Monad.Foil.TH
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

-- ** Scope-safe patterns

mkFoilPattern ''Raw.VarIdent ''Raw.Pattern'
deriveCoSinkable ''Raw.VarIdent ''Raw.Pattern'
mkToFoilPattern ''Raw.VarIdent ''Raw.Pattern'
mkFromFoilPattern ''Raw.VarIdent ''Raw.Pattern'

-- * User-defined code

instance Foil.UnifiablePattern FoilPattern where
  unifyPatterns (FoilPatternWildcard _loc) (FoilPatternWildcard _loc') = Foil.SameNameBinders Foil.emptyNameBinders
  unifyPatterns (FoilPatternVar _loc x) (FoilPatternVar _loc' x') = Foil.unifyNameBinders x x'
  unifyPatterns (FoilPatternPair _loc l r) (FoilPatternPair _loc' l' r') =
    case (Foil.assertDistinct l, Foil.assertDistinct l') of
      (Foil.Distinct, Foil.Distinct) -> Foil.unifyPatterns l l' `Foil.andThenUnifyPatterns` (r, r')
  unifyPatterns _ _ = Foil.NotUnifiable

-- | Generic annotated scope-safe \(\lambda\Pi\)-terms with patterns.
type Term' a = AST (FoilPattern' a) (Term'Sig a)

-- | Scode-safe \(\lambda\Pi\)-terms annotated with source code position.
type Term = Term' Raw.BNFC'Position

-- | Scope-safe patterns annotated with source code position.
type FoilPattern = FoilPattern' Raw.BNFC'Position

-- ** Conversion helpers

-- | Convert 'Raw.Term'' into a scope-safe term.
-- This is a special case of 'convertToAST'.
toTerm' :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term' a -> Term' a n
toTerm' = convertToAST convertToTerm'Sig toFoilPattern' getTerm'FromScopedTerm'

-- | Convert 'Raw.Term'' into a closed scope-safe term.
-- This is a special case of 'toTerm''.
toTerm'Closed :: Raw.Term' a -> Term' a Foil.VoidS
toTerm'Closed = toTerm' Foil.emptyScope Map.empty

-- | Convert a scope-safe representation back into 'Raw.Term''.
-- This is a special case of 'convertFromAST'.
--
-- 'Raw.VarIdent' names are generated based on the raw identifiers in the underlying foil representation.
--
-- This function does not recover location information for variables, patterns, or scoped terms.
fromTerm' :: Term' a n -> Raw.Term' a
fromTerm' = convertFromAST
  convertFromTerm'Sig
  (Raw.Var (error "location missing"))
  fromFoilPattern'
  (Raw.AScopedTerm (error "location missing"))
  (\n -> Raw.VarIdent ("x" ++ show n))

-- | Parse scope-safe terms via raw representation.
--
-- >>> fromString "λx.λy.λx.x" :: Term Foil.VoidS
-- λ x0 . λ x1 . λ x2 . x2
instance IsString (AST FoilPattern (Term'Sig Raw.BNFC'Position) Foil.VoidS) where
  fromString input = case Raw.pTerm (Raw.tokens input) of
    Left err   -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
    Right term -> toTerm'Closed term

-- | Pretty-print scope-safe terms via raw representation.
instance Show (AST (FoilPattern' a) (Term'Sig a) Foil.VoidS) where
  show = Raw.printTree . fromTerm'

-- ** Evaluation

-- | Match a pattern against an term.
matchPattern :: FoilPattern n l -> Term n -> Foil.Substitution Term l n
matchPattern pat term = go pat term Foil.identitySubst
  where
    go :: FoilPattern i l -> Term n -> Foil.Substitution Term i n -> Foil.Substitution Term l n
    go (FoilPatternWildcard _loc) _ = id
    go (FoilPatternVar _loc x) e    = \subst -> Foil.addSubst subst x e
    go (FoilPatternPair loc l r) e  = go r (Second loc e) . go l (First loc e)

-- | Compute weak head normal form (WHNF) of a \(\lambda\Pi\)-term.
--
-- >>> whnf Foil.emptyScope "(λx.(λ_.x)(λy.x))(λ(y,z).z)"
-- λ (x0, x1) . x1
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
        let subst = matchPattern binder x
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

-- ** \(\lambda\Pi\)-interpreter

-- | Interpret a \(\lambda\Pi\) command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute _loc term _type) =
      putStrLn ("  ↦ " ++ show (whnf Foil.emptyScope (toTerm'Closed term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _loc _term _type) = putStrLn "check is not yet implemented"

-- | Interpret a \(\lambda\Pi\) program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram _loc typedTerms) = mapM_ interpretCommand typedTerms

-- | A \(\lambda\Pi\) interpreter implemented via the free foil.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case Raw.pProgram (Raw.resolveLayout True (Raw.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
