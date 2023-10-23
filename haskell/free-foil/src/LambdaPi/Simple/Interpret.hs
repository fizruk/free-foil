{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module LambdaPi.Simple.Interpret where

import Data.List (intercalate)
import System.Exit (exitFailure)

import Language.LambdaPi.Simple.Abs
import Language.LambdaPi.Simple.Lex (tokens)
import Language.LambdaPi.Simple.Layout (resolveLayout)
import Language.LambdaPi.Simple.Par (pProgram)
import Language.LambdaPi.Simple.Print (printTree)

-- | Typecheck a term agains a given type.
--
-- FIXME: typechecking is not complete (or correct) here.
typecheck
  :: Term               -- ^ Term to check.
  -> Term               -- ^ Expected type.
  -> [(Ident, Term)]    -- ^ Known types of variables.
  -> Either String [(Ident, Term)]
typecheck term expectedType scope =
  case term of
    Var x ->
      case lookup x scope of
        Just actualType
          | actualType == expectedType -> return scope
          | otherwise -> Left $ intercalate "\n"
              [ "  Expected type"
              , "    " ++ printTree expectedType
              , "  but got type"
              , "    " ++ printTree actualType
              , "  for term"
              , "    " ++ printTree term ]
        Nothing -> return ((x, expectedType) : scope)

    Lam x body ->
      case expectedType of
        Pi x' xtype bodyType ->
          typecheck body (substitute (x', Var x) bodyType) ((x, whnf xtype) : scope)
        _ -> Left $ intercalate "\n"
              [ "  Expected type"
              , "    " ++ printTree expectedType
              , "  but got Π-type for a λ-abstraction"
              , "    " ++ printTree term ]

    Pi x xtype body ->
      case expectedType of
        Var "Type" -> do
          scope' <- typecheck xtype (Var "Type") scope
          typecheck body (Var "Type") ((x, whnf xtype) : scope')
        _ -> Left $ intercalate "\n"
              [ "  Expected type"
              , "    " ++ printTree expectedType
              , "  but got Type for a Π-type"
              , "    " ++ printTree term ]

    App f arg -> return [] -- FIXME: typechecking for application is not implemented!

-- | Perform a single substitution in a term.
--
-- FIXME: incorrent implementation (name captures!)
substitute :: (Ident, Term) -> Term -> Term
substitute (z, arg) t@(Var y)
  | y == z = arg
  | otherwise = t
substitute (z, arg) (App f x) =
  App (substitute (z, arg) f) (substitute (z, arg) x)
substitute (z, arg) t@(Lam x body)
  | z == x = t
  | otherwise = Lam x (substitute (z, arg) body)
substitute (z, arg) t@(Pi a typeOfA b)
  | z == a = t
  | otherwise = Pi a typeOfA (substitute (z, arg) b)

-- | Compute a λΠ term into its weak head normal form (WHNF).
whnf :: Term -> Term
whnf = \case
  App f arg ->
    case whnf f of
      Lam z body -> substitute (z, arg) body
      f' -> App f' arg
  t -> t

-- | Interpret a λΠ command.
interpretCommand :: Command -> IO ()
interpretCommand (CommandCheck term type_) =
  case typecheck term type_ [] of
    Left err -> putStrLn ("Type Error: " ++ err)
    Right _ -> do
      putStrLn "Term is well-typed:"
      putStrLn ("  " ++ printTree term)
interpretCommand (CommandCompute term type_) =
  case typecheck term type_ [] of
    Left err -> putStrLn ("Type Error: " ++ err)
    Right _ -> do
      putStrLn "Computing"
      putStrLn ("  " ++ printTree term)
      putStrLn ("  ↦ " ++ printTree (whnf term))

-- | Interpret a λΠ program.
interpretProgram :: Program -> IO ()
interpretProgram (AProgram typedTerms) = mapM_ interpretCommand typedTerms

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
