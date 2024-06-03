{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Foil implementation of the \(\lambda\Pi\)-calculus (with pairs).
--
-- The following is implemented manually in this module:
--
-- 1. Scope-safe AST for \(\lambda\Pi\)-terms.
-- 2. Correct capture-avoiding substitution (see 'substitute').
-- 3. Conversion between scope-safe and raw term representation (the latter is generated via BNFC), see 'toFoilTerm' and 'fromFoilTerm'.
-- 4. Computation of weak head normal form (WHNF) and normal form (NF), see 'whnf' and 'nf'.
-- 5. Entry point, gluing everything together. See 'defaultMain'.
--
-- This implementation supports (nested) patterns for pairs.
module Language.LambdaPi.Impl.Foil where

import           Control.Monad.Foil

import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import qualified Language.LambdaPi.Syntax.Abs    as Raw
import           Language.LambdaPi.Syntax.Layout (resolveLayout)
import           Language.LambdaPi.Syntax.Lex    (tokens)
import           Language.LambdaPi.Syntax.Par    (pProgram)
import           Language.LambdaPi.Syntax.Print  (printTree)
import           System.Exit                     (exitFailure)

-- | Type of scope-safe \(\lambda\Pi\)-terms with pairs.
data Expr n where
  -- | Variables: \(x\)
  VarE  :: Name n -> Expr n

  -- | Application: \((t_1 \; t_2)\)
  AppE  :: Expr n -> Expr n -> Expr n
  -- | Abstraction (with patterns): \(\lambda p. t\)
  LamE  :: Pattern n l -> Expr l -> Expr n
  -- | \(\prod\)-types (with patterns): \(\prod_{p : T_1} T_2\)
  PiE   :: Pattern n l -> Expr n -> Expr l -> Expr n

  -- | Pair of terms: \(\langle t_1, t_2 \rangle\)
  PairE :: Expr n -> Expr n -> Expr n
  -- | First projection: \(\pi_1(t)\)
  FirstE :: Expr n -> Expr n
  -- | Second projection: \(\pi_2(t)\)
  SecondE :: Expr n -> Expr n
  -- | Product type (non-dependent): \(T_1 \times T_2\)
  ProductE :: Expr n -> Expr n -> Expr n

  -- | Universe (type of types): \(\mathcal{U}\)
  UniverseE :: Expr n

-- | Patterns.
data Pattern n l where
  -- | Wildcard pattern: \(_\)
  PatternWildcard :: Pattern n n
  -- | Variable pattern: \(x\)
  PatternVar :: NameBinder n l -> Pattern n l
  -- | Pair pattern: \((p_1, p_2)\)
  PatternPair :: Pattern n i -> Pattern i l -> Pattern n l

instance CoSinkable Pattern where
  coSinkabilityProof rename pattern cont =
    case pattern of
      PatternWildcard ->
        cont rename PatternWildcard
      PatternVar x ->
        coSinkabilityProof rename x $ \rename' x' ->
          cont rename' (PatternVar x')
      PatternPair l r ->
        coSinkabilityProof rename l $ \rename' l' ->
          coSinkabilityProof rename' r $ \rename'' r' ->
            cont rename'' (PatternPair l' r')

instance InjectName Expr where
  injectName = VarE

-- | Default way to print a name using its internal 'Id'.
ppName :: Name n -> String
ppName name = "x" <> show (nameId name)

-- | Pretty-print a \(\lambda\Pi\)-term directly (without converting to raw term).
--
-- >>> putStrLn $ ppExpr identity
-- λx1. x1
-- >>> putStrLn $ ppExpr two
-- λx1. λx2. x1(x1(x2))
ppExpr :: Expr n -> String
ppExpr = \case
  VarE name     -> ppName name
  AppE e1 e2    -> ppExpr e1 ++ "(" ++ ppExpr e2 ++ ")"
  LamE pat body -> "λ" ++ ppPattern pat ++ ". " ++ ppExpr body
  PiE pat a b -> "Π" ++ "(" ++ ppPattern pat ++ " : " ++ ppExpr a ++ "), " ++ ppExpr b
  PairE l r -> "(" ++ ppExpr l ++ "," ++ ppExpr r ++ ")"
  FirstE t -> "π₁(" ++ ppExpr t ++ ")"
  SecondE t -> "π₂(" ++ ppExpr t ++ ")"
  ProductE l r -> "(" ++ ppExpr l ++ " × " ++ ppExpr r ++ ")"
  UniverseE -> "𝕌"

-- | Pretty-print a pattern in a \(\lambda\Pi\)-term (without converting to raw pattern)..
ppPattern :: Pattern n l -> String
ppPattern = \case
  PatternWildcard -> "_"
  PatternVar x -> ppName (nameOf x)
  PatternPair l r -> "(" <> ppPattern l <> "," <> ppPattern r <> ")"

-- | Pretty-print a /closed/ scode-safe \(\lambda\Pi\)-term
-- using BNFC-generated printer (via 'Raw.Term').
printExpr :: Expr VoidS -> String
printExpr = printTree . fromFoilTermClosed
  [ Raw.VarIdent ("x" <> show i) | i <- [1 :: Integer ..] ]

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE pat body) = extendRenaming rename pat $ \rename' pat' ->
    LamE pat' (sinkabilityProof rename' body)
  sinkabilityProof rename (PiE pat a b) =
    extendRenaming rename pat $ \rename' pat' ->
      PiE pat' (sinkabilityProof rename a) (sinkabilityProof rename' b)
  sinkabilityProof rename (PairE l r) = PairE (sinkabilityProof rename l) (sinkabilityProof rename r)
  sinkabilityProof rename (FirstE t) = FirstE (sinkabilityProof rename t)
  sinkabilityProof rename (SecondE t) = SecondE (sinkabilityProof rename t)
  sinkabilityProof rename (ProductE l r) = ProductE (sinkabilityProof rename l) (sinkabilityProof rename r)
  sinkabilityProof _ UniverseE = UniverseE

-- | Extend scope with variables inside a pattern.
-- This is a more flexible version of 'extendScope'.
extendScopePattern :: Pattern n l -> Scope n -> Scope l
extendScopePattern = \case
  PatternWildcard -> id
  PatternVar binder -> extendScope binder
  PatternPair l r -> extendScopePattern r . extendScopePattern l

-- | Refresh (if needed) bound variables introduced in a pattern.
-- This is a more flexible version of 'withRefreshed'.
withRefreshedPattern
  :: (Distinct o, InjectName e, Sinkable e)
  => Scope o
  -> Pattern n l
  -> (forall o'. DExt o o' => (Substitution e n o -> Substitution e l o') -> Pattern o o' -> r) -> r
withRefreshedPattern scope pattern cont =
  case pattern of
    PatternWildcard -> cont sink PatternWildcard
    PatternVar x    -> withRefreshed scope (nameOf x) $ \x' ->
      cont (\subst -> addRename (sink subst) x (nameOf x')) (PatternVar x')
    PatternPair l r -> withRefreshedPattern scope l $ \lsubst l' ->
      let scope' = extendScopePattern l' scope
       in withRefreshedPattern scope' r $ \rsubst r' ->
            cont (rsubst . lsubst) (PatternPair l' r')

-- | Perform substitution in a \(\lambda\Pi\)-term.
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE pattern body -> withRefreshedPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          body' = substitute scope' subst' body
       in LamE pattern' body'
    PiE pattern a b -> withRefreshedPattern scope pattern $ \extendSubst pattern' ->
      let subst' = extendSubst subst
          scope' = extendScopePattern pattern' scope
          a' = substitute scope subst a
          b' = substitute scope' subst' b
       in PiE pattern' a' b'
    PairE l r -> PairE (substitute scope subst l) (substitute scope subst r)
    FirstE t -> FirstE (substitute scope subst t)
    SecondE t -> SecondE (substitute scope subst t)
    ProductE l r -> ProductE (substitute scope subst l) (substitute scope subst r)
    UniverseE -> UniverseE

-- | Convert a raw pattern into a scope-safe one.
toFoilPattern
  :: Distinct n
  => Scope n                    -- ^ Outer scope (outside of pattern binding).
  -> Map Raw.VarIdent (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> Raw.Pattern                -- ^ Raw pattern.
  -> (forall l. DExt n l => Pattern n l -> Map Raw.VarIdent (Name l) -> r)
  -- ^ A continuation, accepting a scope-safe pattern and an updated variable mapping.
  -> r
toFoilPattern scope env pattern cont =
  case pattern of
    Raw.PatternWildcard -> cont PatternWildcard env
    Raw.PatternVar x -> withFresh scope $ \binder ->
      cont (PatternVar binder) (Map.insert x (nameOf binder) (sink <$> env))
    Raw.PatternPair l r ->
      toFoilPattern scope env l $ \l' env' ->
        let scope' = extendScopePattern l' scope
         in toFoilPattern scope' env' r $ \r' env'' ->
              cont (PatternPair l' r') env''

-- | Convert a scope-safe pattern into a raw pattern.
fromFoilPattern
  :: [Raw.VarIdent]         -- ^ A stream of fresh variable identifiers.
  -> NameMap n Raw.VarIdent -- ^ A /total/ mapping for names in scope @n@.
  -> Pattern n l            -- ^ A scope-safe pattern that extends scope @n@ into scope @l@.
  -> ([Raw.VarIdent] -> NameMap l Raw.VarIdent -> Raw.Pattern -> r)
    -- ^ A continutation, accepting (smaller) stream of fresh variable identifiers, a mapping for the inner scope, and a raw pattern.
  -> r
fromFoilPattern freshVars env pattern cont =
  case pattern of
    PatternWildcard -> cont freshVars env Raw.PatternWildcard
    PatternVar z ->
      case freshVars of
        []   -> error "not enough fresh variables!"
        x:xs -> cont xs (addNameBinder z x env) (Raw.PatternVar x)
    PatternPair l r ->
      fromFoilPattern freshVars env l $ \freshVars' env' l' ->
        fromFoilPattern freshVars' env' r $ \freshVars'' env'' r' ->
          cont freshVars'' env'' (Raw.PatternPair l' r')

-- | Convert a scope-safe term into a raw term.
fromFoilTerm
  :: [Raw.VarIdent]         -- ^ A stream of fresh variable identifiers.
  -> NameMap n Raw.VarIdent -- ^ A /total/ mapping for names in scope @n@.
  -> Expr n                 -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTerm freshVars env = \case
  VarE name -> Raw.Var (lookupName name env)
  AppE t1 t2 -> Raw.App (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  LamE pattern body ->
    fromFoilPattern freshVars env pattern $ \freshVars' env' pattern' ->
      Raw.Lam pattern' (Raw.AScopedTerm (fromFoilTerm freshVars' env' body))
  PiE pattern a b ->
    fromFoilPattern freshVars env pattern $ \freshVars' env' pattern' ->
      Raw.Pi pattern' (fromFoilTerm freshVars env a) (Raw.AScopedTerm (fromFoilTerm freshVars' env' b))
  PairE t1 t2 -> Raw.Pair (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  FirstE t -> Raw.First (fromFoilTerm freshVars env t)
  SecondE t -> Raw.Second (fromFoilTerm freshVars env t)
  ProductE t1 t2 -> Raw.Product (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  UniverseE -> Raw.Universe

-- | Convert a /closed/ scope-safe term into a raw term.
fromFoilTermClosed
  :: [Raw.VarIdent]   -- ^ A stream of fresh variable identifiers.
  -> Expr VoidS       -- ^ A scope safe term in scope @n@.
  -> Raw.Term
fromFoilTermClosed freshVars = fromFoilTerm freshVars emptyNameMap

-- | Convert a raw term into a scope-safe \(\lambda\Pi\)-term.
toFoilTerm
  :: Distinct n
  => Scope n                    -- ^ Target scope.
  -> Map Raw.VarIdent (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> Raw.Term                   -- ^ A raw term.
  -> Expr n
toFoilTerm scope env = \case
  Raw.Var x ->
    case Map.lookup x env of
      Just name -> VarE name
      Nothing   -> error $ "unknown free variable: " <> show x

  Raw.App t1 t2 ->
    AppE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  Raw.Lam pattern (Raw.AScopedTerm body) ->
    toFoilPattern scope env pattern $ \pattern' env' ->
      let scope' = extendScopePattern pattern' scope
       in LamE pattern' (toFoilTerm scope' env' body)

  Raw.Pi pattern a (Raw.AScopedTerm b) ->
    toFoilPattern scope env pattern $ \pattern' env' ->
      let scope' = extendScopePattern pattern' scope
       in PiE pattern' (toFoilTerm scope env a) (toFoilTerm scope' env' b)

  Raw.Pair t1 t2 ->
    PairE (toFoilTerm scope env t1) (toFoilTerm scope env t2)
  Raw.First t ->
    FirstE (toFoilTerm scope env t)
  Raw.Second t ->
    SecondE (toFoilTerm scope env t)

  Raw.Product t1 t2 ->
    ProductE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  Raw.Universe -> UniverseE

-- | Match a pattern against an expression.
matchPattern :: Pattern n l -> Expr n -> Substitution Expr l n
matchPattern pattern expr = go pattern expr identitySubst
  where
    go :: Pattern i l -> Expr n -> Substitution Expr i n -> Substitution Expr l n
    go PatternWildcard _   = id
    go (PatternVar x) e    = \subst -> addSubst subst x e
    go (PatternPair l r) e = go r (SecondE e) . go l (FirstE e)

-- | Compute weak head normal form (WHNF).
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE f arg ->
    case whnf scope f of
      LamE pat body ->
        let subst = matchPattern pat arg
         in whnf scope (substitute scope subst body)
      f' -> AppE f' arg
  FirstE t ->
    case whnf scope t of
      PairE l _r -> whnf scope l
      t'         -> FirstE t'
  SecondE t ->
    case whnf scope t of
      PairE _l r -> whnf scope r
      t'         -> SecondE t'
  t -> t

-- | Interpret a λΠ command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute term _type) =
  putStrLn ("  ↦ " ++ printExpr (whnf emptyScope (toFoilTerm emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _term _type) =
  putStrLn "Not yet implemented"

-- | Interpret a λΠ program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram typedTerms) = mapM_ interpretCommand typedTerms

-- | Default interpreter program.
-- Reads a λΠ program from the standard input and runs the commands.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case pProgram (resolveLayout True (tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
