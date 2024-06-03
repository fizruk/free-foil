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
{-# LANGUAGE UndecidableInstances  #-}

module Language.LambdaPi.Impl.FoilBnfc where

import           Control.Monad.Foil
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.String                     (String)
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

  -- | Application: \((t_1 t_2)\)
  AppE  :: Expr n -> Expr n -> Expr n
  -- | Abstraction (with patterns): \(\lambda p. t\)
  LamE  :: Pattern n l -> Expr l -> Expr n
  -- | \(\prod\)-types (with patterns): \(\prod_{p : T_1}. T_2\)
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

ppName :: Name n -> String
ppName name = "x" <> show (nameId name)

-- | Pretty-print a \(\lambda\Pi\)-term.AST
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

-- | Pretty-print a pattern in a \(\lambda\Pi\)-term.
ppPattern :: Pattern n l -> String
ppPattern = \case
  PatternWildcard -> "_"
  PatternVar x -> ppName (nameOf x)
  PatternPair l r -> "(" <> ppPattern l <> "," <> ppPattern r <> ")"

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder \rename' pat' ->
    LamE pat' (sinkabilityProof rename' body)

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
      withRefreshedPattern (extendScopePattern l' scope) r $ \rsubst r' ->
        cont (rsubst . lsubst) (PatternPair l' r')

-- | Perform substitution in a \(\lambda\Pi\)-term.
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE pattern body -> withRefreshedPattern scope pattern (\extendSubst pattern' ->
        let subst' = extendSubst subst
            scope' = extendScopePattern pattern' scope
            body' = substitute scope' subst' body in LamE pattern' body'
        )

toFoilPattern
  :: Distinct n
  => Scope n                    -- ^ Outer scope (outside of pattern binding).
  -> Map Raw.VarIdent (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> Raw.Pattern                -- ^ Raw pattern.
  -> (forall l. DExt n l => Pattern n l -> Map Raw.VarIdent (Name l) -> r)
  -- ^ Continuation, accepting a scope-safe pattern and an updated variable mapping.
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

-- | Convert a raw term into a scope-safe \(\lambda\Pi\)-term.
toFoilTerm :: Distinct n => Scope n -> Map Raw.VarIdent (Name n) -> Raw.Term -> Expr n
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

  Raw.Pair t1 t2 ->
    PairE (toFoilTerm scope env t1) (toFoilTerm scope env t2)
  Raw.First t ->
    FirstE (toFoilTerm scope env t)
  Raw.Second t ->
    SecondE (toFoilTerm scope env t)

  Raw.Product t1 t2 ->
    ProductE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  Raw.Universe -> UniverseE

-- toFoilTerm (Raw.App a b) scope env = AppE (toFoilTerm a scope env) (toFoilTerm b scope env)
-- toFoilTerm (Raw.Lam (Raw.PatternVar (Raw.VarIdent str)) (Raw.AScopedTerm body)) scope env = withFresh scope (\s ->
--   let scope' = extendScope s scope
--       env' = Map.insert str (nameOf s) (fmap sink env) in LamE (PatternVar s) (toFoilTerm body scope' env'))
-- toFoilTerm (Raw.Var (Raw.VarIdent str)) scope env = case Map.lookup str env of
--   Just name -> VarE name
--   Nothing   -> error ("Unbound variable " ++ str)
-- -- #TODO: suppori Pi expressions
-- toFoilTerm Raw.Pi{} scope env = error "Not yet implemented"

matchPattern :: Pattern n l -> Expr n -> Substitution Expr l n
matchPattern PatternWildcard _ = identitySubst

whnf :: (Distinct n) => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE f arg ->
    case whnf scope f of
      LamE pat body ->
        let subst = matchPattern pat arg
         in substitute scope subst body
      f' -> AppE f' arg
  t -> t

-- | Interpret a λΠ command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute term type_) =
      putStrLn ("  ↦ " ++ ppExpr (whnf emptyScope (toFoilTerm emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck term type_) =
      putStrLn "Not yet implemented"

-- | Interpret a λΠ program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram typedTerms) = mapM_ interpretCommand typedTerms

-- | Default interpreter program.
-- Reads a λΠ program from the standard input and runs the commands.
foilMain :: IO ()
foilMain = do
  input <- getContents
  case pProgram (resolveLayout True (tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
