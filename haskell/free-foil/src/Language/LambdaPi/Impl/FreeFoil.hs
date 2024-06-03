{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.LambdaPi.Impl.FreeFoil where

import qualified Control.Monad.Foil              as Foil
import           Control.Monad.Free.Foil
import           Data.Bifunctor
import           Data.Bifunctor.TH
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import qualified Language.LambdaPi.Syntax.Abs    as Syntax
import qualified Language.LambdaPi.Syntax.Layout as Syntax
import qualified Language.LambdaPi.Syntax.Lex    as Syntax
import qualified Language.LambdaPi.Syntax.Par    as Syntax
import qualified Language.LambdaPi.Syntax.Print  as Print
import           System.Exit                     (exitFailure)

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
        let subst = Foil.addSubst Foil.identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

toLambdaPi :: Foil.Distinct n => Foil.Scope n -> Map String (Foil.Name n) -> Syntax.Term -> LambdaPi n
toLambdaPi scope env = \case
  Syntax.Var (Syntax.VarIdent x) ->
    case Map.lookup x env of
      Just name -> Var name
      Nothing   -> error ("unbound variable: " ++ x)

  Syntax.App fun arg ->
    App (toLambdaPi scope env fun) (toLambdaPi scope env arg)

  Syntax.Lam (Syntax.PatternVar (Syntax.VarIdent x)) (Syntax.AScopedTerm body) -> Foil.withFresh scope $ \binder ->
    let scope' = Foil.extendScope binder scope
        env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
    in Lam binder (toLambdaPi scope' env' body)

  Syntax.Pi (Syntax.PatternVar (Syntax.VarIdent x)) a (Syntax.AScopedTerm b) -> Foil.withFresh scope $ \binder ->
    let scope' = Foil.extendScope binder scope
        env' = Map.insert x (Foil.nameOf binder) (Foil.sink <$> env)
    in Pi binder (toLambdaPi scope env a) (toLambdaPi scope' env' b)

fromLambdaPi :: LambdaPi n -> Syntax.Term
fromLambdaPi = \case
  Var name -> Syntax.Var (Syntax.VarIdent (ppName name))
  App fun arg -> Syntax.App (fromLambdaPi fun) (fromLambdaPi arg)
  Lam binder body ->
    let x = Foil.nameOf binder
    in Syntax.Lam (Syntax.PatternVar (Syntax.VarIdent (ppName x))) (Syntax.AScopedTerm (fromLambdaPi body))
  Pi binder a b ->
    let x = Foil.nameOf binder
    in Syntax.Pi (Syntax.PatternVar (Syntax.VarIdent (ppName x))) (fromLambdaPi a) (Syntax.AScopedTerm (fromLambdaPi b))

ppLambdaPi :: LambdaPi n -> String
ppLambdaPi = Print.printTree . fromLambdaPi

ppName :: Foil.Name n -> String
ppName name = "x" <> show (Foil.nameId name)

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
