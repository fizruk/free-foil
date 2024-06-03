{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.LambdaPi.Impl.FreeFoil where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor.TH
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import qualified Language.LambdaPi.Syntax.Abs    as Raw
import qualified Language.LambdaPi.Syntax.Layout as Raw
import qualified Language.LambdaPi.Syntax.Lex    as Raw
import qualified Language.LambdaPi.Syntax.Par    as Raw
import qualified Language.LambdaPi.Syntax.Print  as Print
import qualified Language.LambdaPi.Syntax.Print  as Raw
import           System.Exit                     (exitFailure)

data LambdaPiF scope term
  = AppF term term
  | LamF scope
  | PiF term scope
  | PairF term term
  | FirstF term
  | SecondF term
  | ProductF term term
  | UniverseF
  deriving (Eq, Show, Functor)
deriveBifunctor ''LambdaPiF

type LambdaPi n = AST LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: Foil.NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

pattern Pi :: Foil.NameBinder n l -> LambdaPi n -> LambdaPi l -> LambdaPi n
pattern Pi binder a b = Node (PiF a (ScopedAST binder b))

pattern Pair :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern Pair l r = Node (PairF l r)

pattern First :: LambdaPi n -> LambdaPi n
pattern First t = Node (FirstF t)

pattern Second :: LambdaPi n -> LambdaPi n
pattern Second t = Node (SecondF t)

pattern Product :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern Product l r = Node (ProductF l r)

pattern Universe :: LambdaPi n
pattern Universe = Node UniverseF

{-# COMPLETE Var, App, Lam, Pi, Pair, First, Second, Product, Universe #-}

whnf :: Foil.Distinct n => Foil.Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = Foil.addSubst Foil.identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

toLambdaPiLam :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Pattern -> Raw.ScopedTerm -> LambdaPi n
toLambdaPiLam scope env pat (Raw.AScopedTerm body) =
  case pat of
    Raw.PatternWildcard -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
       in Lam binder (toLambdaPi scope' (Foil.sink <$> env) body)

    Raw.PatternVar x -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
          env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
       in Lam binder (toLambdaPi scope' env' body)

    Raw.PatternPair{} -> error "pattern pairs are not supported in the FreeFoil example"

toLambdaPiPi :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Pattern -> Raw.Term -> Raw.ScopedTerm -> LambdaPi n
toLambdaPiPi scope env pat a (Raw.AScopedTerm b) =
  case pat of
    Raw.PatternWildcard -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
       in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' (Foil.sink <$> env) b)

    Raw.PatternVar x -> Foil.withFresh scope $ \binder ->
      let scope' = Foil.extendScope binder scope
          env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
       in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' env' b)

    Raw.PatternPair{} -> error "pattern pairs are not supported in the FreeFoil example"

toLambdaPi :: Foil.Distinct n => Foil.Scope n -> Map Raw.VarIdent (Foil.Name n) -> Raw.Term -> LambdaPi n
toLambdaPi scope env = \case
  Raw.Var x ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing   -> error ("unbound variable: " ++ Raw.printTree x)

  Raw.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  Raw.Lam pat body -> toLambdaPiLam scope env pat body
  Raw.Pi pat a b -> toLambdaPiPi scope env pat a b

  Raw.Pair l r -> Pair (toLambdaPi scope env l) (toLambdaPi scope env r)
  Raw.First t -> First (toLambdaPi scope env t)
  Raw.Second t -> Second (toLambdaPi scope env t)
  Raw.Product l r -> Product (toLambdaPi scope env l) (toLambdaPi scope env r)

  Raw.Universe -> Universe

fromLambdaPi :: LambdaPi n -> Raw.Term
fromLambdaPi = \case
  Var name -> Raw.Var (Raw.VarIdent (ppName name))
  App fun arg -> Raw.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let x = Foil.nameOf binder
    in Raw.Lam (Raw.PatternVar (Raw.VarIdent (ppName x))) (Raw.AScopedTerm (fromLambdaPi body))
  Pi binder a b ->
    let x = Foil.nameOf binder
    in Raw.Pi (Raw.PatternVar (Raw.VarIdent (ppName x))) (fromLambdaPi a) (Raw.AScopedTerm (fromLambdaPi b))
  Pair l r -> Raw.Pair (fromLambdaPi l) (fromLambdaPi r)
  First t -> Raw.First (fromLambdaPi t)
  Second t -> Raw.Second (fromLambdaPi t)
  Product l r -> Raw.Product (fromLambdaPi l) (fromLambdaPi r)
  Universe -> Raw.Universe

ppLambdaPi :: LambdaPi n -> String
ppLambdaPi = Print.printTree . fromLambdaPi

ppName :: Foil.Name n -> String
ppName name = "x" <> show (Foil.nameId name)

-- | Interpret a λΠ command.
interpretCommand :: Raw.Command -> IO ()
interpretCommand (Raw.CommandCompute term _type) =
      putStrLn ("  ↦ " ++ ppLambdaPi (whnf Foil.emptyScope (toLambdaPi Foil.emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Raw.CommandCheck _term _type) = putStrLn "check is not yet implemented"

-- | Interpret a λΠ program.
interpretProgram :: Raw.Program -> IO ()
interpretProgram (Raw.AProgram typedTerms) = mapM_ interpretCommand typedTerms

main :: IO ()
main = do
  input <- getContents
  case Raw.pProgram (Raw.resolveLayout True (Raw.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
