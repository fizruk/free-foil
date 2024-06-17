{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- | Free foil implementation of the \(\lambda\Pi\)-calculus (with pairs).
--
-- Free foil provides the following:
--
-- 1. Freely generated (from a simple signature) scope-safe AST.
-- 2. Correct capture-avoiding substitution (see 'substitute').
-- 3. Convenient pattern synonyms (FIXME: use TH to generate those).
--
-- The following is implemented manually in this module:
--
-- 1. Conversion between scope-safe and raw term representation (the latter is generated via BNFC), see 'toLambdaPi' and 'fromLambdaPi'.
-- 2. Computation of weak head normal form (WHNF), see 'whnf'.
-- 3. Entry point, gluing everything together. See 'defaultMain'.
--
-- __Note:__ free foil does not (easily) support patterns at the moment,
-- so only wildcard patterns and variable patterns are handled in this implementation.
module Language.LambdaPi.Impl.FreeFoil where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Free.Foil
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
-- >>> import qualified Control.Monad.Foil as Foil
-- >>> :set -XOverloadedStrings

-- | The signature 'Bifunctor' for the \(\lambda\Pi\).
data LambdaPiF scope term
  = AppF term term        -- ^ Application: \((t_1 \; t_2)\)
  | LamF scope            -- ^ Abstraction: \(\lambda x. t\)
  | PiF term scope        -- ^ Dependent function type: \(\prod_{x : T_1} T_2\)
  | UniverseF             -- ^ Universe (type of types): \(\mathcal{U}\)
  deriving (Eq, Show, Functor)
deriveBifunctor ''LambdaPiF

-- | The signature 'Bifunctor' for pairs.
data PairF scope term
  = PairF term term       -- ^ Pair: \(\langle t_1, t_2 \rangle\)
  | FirstF term           -- ^ First projection: \(\pi_1(t)\)
  | SecondF term          -- ^ Second projection: \(\pi_2(t)\)
  | ProductF term term    -- ^ Product type (non-dependent): \(T_1 \times T_2\)
  deriving (Eq, Show, Functor)
deriveBifunctor ''PairF

-- | Sum of signature bifunctors.
data (f :+: g) scope term
  = InL (f scope term)
  | InR (g scope term)
  deriving (Eq, Show, Functor)
deriveBifunctor ''(:+:)

-- | \(\lambda\Pi\)-terms in scope @n@, freely generated from the sum of signatures 'LambdaPiF' and 'PairF'.
type LambdaPi n = AST (LambdaPiF :+: PairF) n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (InL (AppF fun arg))

pattern Lam :: Foil.NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (InL (LamF (ScopedAST binder body)))

pattern Pi :: Foil.NameBinder n l -> LambdaPi n -> LambdaPi l -> LambdaPi n
pattern Pi binder a b = Node (InL (PiF a (ScopedAST binder b)))

pattern Pair :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern Pair l r = Node (InR (PairF l r))

pattern First :: LambdaPi n -> LambdaPi n
pattern First t = Node (InR (FirstF t))

pattern Second :: LambdaPi n -> LambdaPi n
pattern Second t = Node (InR (SecondF t))

pattern Product :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern Product l r = Node (InR (ProductF l r))

pattern Universe :: LambdaPi n
pattern Universe = Node (InL UniverseF)

{-# COMPLETE Var, App, Lam, Pi, Pair, First, Second, Product, Universe #-}

-- | \(\lambda\Pi\)-terms are pretty-printed using BNFC-generated printer via 'Raw.Term'.
instance Show (LambdaPi Foil.VoidS) where
  show = ppLambdaPi

-- | \(\lambda\Pi\)-terms can be (unsafely) parsed from a 'String' via 'Raw.Term'.
instance IsString (LambdaPi Foil.VoidS) where
  fromString input =
    case Raw.pTerm (Raw.tokens input) of
      Left err -> error ("could not parse λΠ-term: " <> input <> "\n  " <> err)
      Right term -> toLambdaPiClosed term

-- | Compute weak head normal form (WHNF) of a \(\lambda\Pi\)-term.
--
-- >>> whnf Foil.emptyScope "(λx.(λ_.x)(λy.x))(λy.λz.z)"
-- λ x1 . λ x2 . x2
--
-- >>> whnf Foil.emptyScope "(λs.λz.s(s(z)))(λs.λz.s(s(z)))"
-- λ x1 . (λ x2 . λ x3 . x2 (x2 x3)) ((λ x2 . λ x3 . x2 (x2 x3)) x1)
whnf :: Foil.Distinct n => Foil.Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = Foil.addSubst Foil.identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  First t ->
    case whnf scope t of
      Pair l _r -> whnf scope l
      t'        -> First t'
  Second t ->
    case whnf scope t of
      Pair _l r -> whnf scope r
      t'        -> Second t'
  t -> t

-- | Convert a raw \(\lambda\)-abstraction into a scope-safe \(\lambda\Pi\)-term.
toLambdaPiLam
  :: Foil.Distinct n
  => Foil.Scope n                   -- ^ Target scope of the \(\lambda\Pi\)-term.
  -> Map Raw.VarIdent (Foil.Name n) -- ^ Mapping for the free variables in the raw term.
  -> Raw.Pattern                    -- ^ Raw pattern (argument) of the \(\lambda\)-abstraction.
  -> Raw.ScopedTerm                 -- ^ Raw body of the \(\lambda\)-abstraction.
  -> LambdaPi n
toLambdaPiLam scope env pat (Raw.AScopedTerm _loc body) =
  case pat of
    Raw.PatternWildcard _loc -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
       in Lam binder (toLambdaPi scope' (Foil.sink <$> env) body)

    Raw.PatternVar _loc x -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
          env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
       in Lam binder (toLambdaPi scope' env' body)

    Raw.PatternPair{} -> error "pattern pairs are not supported in the FreeFoil example"

-- | Convert a raw \(\Pi\)-type into a scope-safe \(\lambda\Pi\)-term.
toLambdaPiPi
  :: Foil.Distinct n
  => Foil.Scope n                   -- ^ Target scope of the \(\lambda\Pi\)-term.
  -> Map Raw.VarIdent (Foil.Name n) -- ^ Mapping for the free variables in the raw term.
  -> Raw.Pattern                    -- ^ Raw argument pattern of the \(\Pi\)-type.
  -> Raw.Term                       -- ^ Raw argument type of the \(\Pi\)-type.
  -> Raw.ScopedTerm                 -- ^ Raw body (result type family) of the \(\Pi\)-type.
  -> LambdaPi n
toLambdaPiPi scope env pat a (Raw.AScopedTerm _loc b) =
  case pat of
    Raw.PatternWildcard _loc -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
       in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' (Foil.sink <$> env) b)

    Raw.PatternVar _loc x -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
          env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
       in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' env' b)

    Raw.PatternPair{} -> error "pattern pairs are not supported in the FreeFoil example"

-- | Convert a raw expression into a scope-safe \(\lambda\Pi\)-term.
toLambdaPi
  :: Foil.Distinct n
  => Foil.Scope n                   -- ^ Target scope of the \(\lambda\Pi\)-term.
  -> Map Raw.VarIdent (Foil.Name n) -- ^ Mapping for the free variables in the raw term.
  -> Raw.Term                       -- ^ Raw expression or type.
  -> LambdaPi n
toLambdaPi scope env = \case
  Raw.Var _loc x ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing   -> error ("unbound variable: " ++ Raw.printTree x)

  Raw.App _loc fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  Raw.Lam _loc pat body -> toLambdaPiLam scope env pat body
  Raw.Pi _loc pat a b -> toLambdaPiPi scope env pat a b

  Raw.Pair _loc l r -> Pair (toLambdaPi scope env l) (toLambdaPi scope env r)
  Raw.First _loc t -> First (toLambdaPi scope env t)
  Raw.Second _loc t -> Second (toLambdaPi scope env t)
  Raw.Product _loc l r -> Product (toLambdaPi scope env l) (toLambdaPi scope env r)

  Raw.Universe _loc -> Universe

-- | Convert a raw expression into a /closed/ scope-safe \(\lambda\Pi\)-term.
toLambdaPiClosed :: Raw.Term -> LambdaPi Foil.VoidS
toLambdaPiClosed = toLambdaPi Foil.emptyScope Map.empty

-- | Convert back from a scope-safe \(\lambda\Pi\)-term into a raw expression or type.
fromLambdaPi
  :: [Raw.VarIdent]               -- ^ Stream of fresh raw identifiers.
  -> Foil.NameMap n Raw.VarIdent  -- ^ A /total/ map for all names in scope @n@.
  -> LambdaPi n                   -- ^ A scope-safe \(\lambda\Pi\)-term.
  -> Raw.Term
fromLambdaPi freshVars env = \case
  Var name -> Raw.Var loc (Foil.lookupName name env)
  App fun arg -> Raw.App loc (fromLambdaPi freshVars env fun) (fromLambdaPi freshVars env arg)
  Lam binder body ->
    case freshVars of
      [] -> error "not enough fresh variables"
      x:freshVars' ->
        let env' = Foil.addNameBinder binder x env
         in Raw.Lam loc (Raw.PatternVar loc x) (Raw.AScopedTerm loc (fromLambdaPi freshVars' env' body))
  Pi binder a b ->
    case freshVars of
      [] -> error "not enough fresh variables"
      x:freshVars' ->
        let env' = Foil.addNameBinder binder x env
         in Raw.Pi loc (Raw.PatternVar loc x) (fromLambdaPi freshVars env a) (Raw.AScopedTerm loc (fromLambdaPi freshVars' env' b))
  Pair l r -> Raw.Pair loc (fromLambdaPi freshVars env l) (fromLambdaPi freshVars env r)
  First t -> Raw.First loc (fromLambdaPi freshVars env t)
  Second t -> Raw.Second loc (fromLambdaPi freshVars env t)
  Product l r -> Raw.Product loc (fromLambdaPi freshVars env l) (fromLambdaPi freshVars env r)
  Universe -> Raw.Universe loc
  where
    loc = error "no location info available when converting from an AST"

-- | Pretty-print a /closed/ \(\lambda\Pi\)-term.
ppLambdaPi :: LambdaPi Foil.VoidS -> String
ppLambdaPi = Raw.printTree . fromLambdaPi [ Raw.VarIdent ("x" <> show i) | i <- [1 :: Integer ..] ] Foil.emptyNameMap

-- | Interpret a λΠ command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute _loc term _type) =
      putStrLn ("  ↦ " ++ ppLambdaPi (whnf Foil.emptyScope (toLambdaPi Foil.emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _loc _term _type) = putStrLn "check is not yet implemented"

-- | Interpret a λΠ program.
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
