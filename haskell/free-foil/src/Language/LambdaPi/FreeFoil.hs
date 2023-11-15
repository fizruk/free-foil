{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.LambdaPi.FreeFoil where

import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Map (Map)
import System.Exit (exitFailure)
import qualified Data.Map as Map
import qualified Language.LambdaPi.Foil as Foil
import qualified Language.LambdaPi.Simple.Abs as Syntax
import qualified Language.LambdaPi.Simple.Par as Syntax
import qualified Language.LambdaPi.Simple.Lex as Syntax
import qualified Language.LambdaPi.Simple.Layout as Syntax
import qualified Language.LambdaPi.Simple.Print as Print

data ScopedAST sig n where
  ScopedAST :: Foil.NameBinder n l -> AST sig l -> ScopedAST sig n

data AST sig n where
  Var :: Foil.Name n -> AST sig n
  Node :: sig (ScopedAST sig n) (AST sig n) -> AST sig n

instance Bifunctor sig => Foil.Sinkable (AST sig) where
  -- sinkabilityProof :: (Name n -> Name l) -> AST sig n -> AST sig l
  sinkabilityProof rename = \case
    Var name -> Var (rename name)
    Node node -> Node (bimap f (Foil.sinkabilityProof rename) node)
    where
      f (ScopedAST binder body) =
        Foil.extendRenaming rename binder $ \rename' binder' ->
          ScopedAST binder' (Foil.sinkabilityProof rename' body)

substitute
  :: (Bifunctor sig, Foil.Distinct o)
  => Foil.Scope o
  -> Foil.Substitution (AST sig) i o
  -> AST sig i
  -> AST sig o
substitute scope subst = \case
  Var name -> Foil.lookupSubst subst name
  Node node -> Node (bimap f (substitute scope subst) node)
  where
    f (ScopedAST binder body) =
      Foil.withRefreshed scope (Foil.nameOf binder) $ \binder' ->
        let subst' = Foil.addRename (Foil.sink subst) binder (Foil.nameOf binder')
            scope' = Foil.extendScope binder' scope
            body' = substitute scope' subst' body
        in ScopedAST binder' body'

data LambdaPiF scope term
  = AppF term term
  | LamF scope
  | PiF term scope
  deriving (Eq, Show, Functor)
deriveBifunctor ''LambdaPiF

type LambdaPi n = AST LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: Foil.NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

pattern Pi :: Foil.NameBinder n l -> LambdaPi n -> LambdaPi l -> LambdaPi n
pattern Pi binder a b = Node (PiF a (ScopedAST binder b))

{-# COMPLETE Var, App, Lam, Pi #-}

whnf :: Foil.Distinct n => Foil.Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = Foil.addSubst (Foil.identitySubst Var) binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

toLambdaPi :: Foil.Distinct n => Foil.Scope n -> Map String (Foil.Name n) -> Syntax.Term -> LambdaPi n
toLambdaPi scope env = \case
  Syntax.Var (Syntax.Ident x) ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing -> error ("unbound variable: " ++ x)

  Syntax.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  Syntax.Lam (Syntax.Ident x) body -> Foil.withFresh scope $ \binder ->
    let scope' = Foil.extendScope binder scope
        env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
    in Lam binder (toLambdaPi scope' env' body)

  Syntax.Pi (Syntax.Ident x) a b -> Foil.withFresh scope $ \binder ->
    let scope' = Foil.extendScope binder scope
        env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
    in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' env' b)

fromLambdaPi :: LambdaPi n -> Syntax.Term
fromLambdaPi = \case
  Var (Foil.UnsafeName name) -> Syntax.Var (Syntax.Ident ("x" <> show name))
  App fun arg -> Syntax.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let Foil.UnsafeName x = Foil.nameOf binder
    in Syntax.Lam (Syntax.Ident ("x" <> show x)) (fromLambdaPi body)
  Pi binder a b ->
    let Foil.UnsafeName x = Foil.nameOf binder
    in Syntax.Pi (Syntax.Ident ("x" <> show x)) (fromLambdaPi a) (fromLambdaPi b)

ppLambdaPi :: LambdaPi n -> String
ppLambdaPi = Print.printTree . fromLambdaPi

-- | Interpret a λΠ command.
interpretCommand :: Syntax.Command -> IO ()
interpretCommand (Syntax.CommandCompute term type_) =
      putStrLn ("  ↦ " ++ ppLambdaPi (whnf Foil.emptyScope (toLambdaPi Foil.emptyScope Map.empty term)))
-- #TODO: add typeCheck
interpretCommand (Syntax.CommandCheck term type_) =
      putStrLn ("check is not yet implemented")

-- | Interpret a λΠ program.
interpretProgram :: Syntax.Program -> IO ()
interpretProgram (Syntax.AProgram typedTerms) = mapM_ interpretCommand typedTerms

main :: IO ()
main = do
  input <- getContents
  case Syntax.pProgram (Syntax.resolveLayout True (Syntax.tokens input)) of
    Left err -> do
      putStrLn err
      exitFailure
    Right program -> interpretProgram program
