{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The MLTT interpreter: the generated syntax, the evaluator and the type
-- checker glued into a program that reads a file of commands.
--
-- Three commands are understood:
--
-- > def id : Π (A : 𝕌) → A → A := λ A . λ x . x ;
-- > check id : Π (A : 𝕌) → A → A ;
-- > compute id 𝟙 tt ;
--
-- A @def@ extends the ambient scope with one more name, so the loop that
-- interprets a program is polymorphic in the scope and threads a 'Ctx' through
-- it. That is the whole of the top-level environment for now: a top-level
-- constant is an ordinary 'Foil.Name' whose 'Def' is its body.
module Language.MLTT.Impl where

import qualified Control.Monad.Foil           as Foil
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import           Language.MLTT.Eval
import           Language.MLTT.FreeFoilConfig (intToVarIdent)
import           Language.MLTT.Impl.Generated
import qualified Language.MLTT.Syntax.Abs     as Raw
import           Language.MLTT.Typecheck
import           System.Exit                  (exitFailure)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XDataKinds

-- * The top-level environment

-- | Names of the definitions made so far, and of nothing else: the top level
-- has no local variables.
type TopEnv n = Map Raw.VarIdent (Foil.Name n)

-- | How to print a free variable: a top-level definition by the name it was
-- given, and anything else by its allocated index.
--
-- This is the read-back direction of 'TopEnv', and is the seed of the interner
-- a module layer would need: a 'Foil.Name' is an allocation artefact, so
-- printing it — and, later, writing it to disk — has to go through a table.
type Display = Map Int Raw.VarIdent

-- | Print a term, showing top-level definitions by name.
display :: Display -> Term n -> String
display names = showTermWith (\i -> Map.findWithDefault (intToVarIdent i) i names)

-- | Convert a raw term into a scope-safe, desugared one.
toTerm :: Foil.Distinct n => Ctx Raw.BNFC'Position n -> TopEnv n -> Raw.Term -> Term n
toTerm ctx env = desugar . toTerm' (ctxScope ctx) env

-- * Interpreting a program

-- | What interpreting one command produced.
data CommandResult
  = Defined String            -- ^ @def@ succeeded, for the named definition.
  | Checked String String     -- ^ @check@ succeeded, for a term and its type.
  | Computed String           -- ^ @compute@ succeeded, with the normal form.
  | Failed TypeError          -- ^ The command was rejected.
  deriving (Eq, Show)

-- | Did every command succeed?
succeeded :: [CommandResult] -> Bool
succeeded = all $ \case
  Failed _ -> False
  _        -> True

-- | Render a result the way the executable prints it.
renderResult :: CommandResult -> String
renderResult = \case
  Defined name     -> "  ✓ defined " <> name
  Checked term ty  -> "  ✓ " <> term <> " : " <> ty
  Computed term    -> "  ↦ " <> term
  Failed err       -> "  ✗ " <> err

-- | Interpret a program, threading the growing top-level scope through the
-- commands.
--
-- A command that fails does not stop the program: the remaining commands are
-- still interpreted, in the environment as it stood.
interpretProgram :: Raw.Program -> [CommandResult]
interpretProgram (Raw.AProgram _loc commands) = go emptyCtx Map.empty Map.empty commands
  where
    go
      :: Foil.Distinct n
      => Ctx Raw.BNFC'Position n -> TopEnv n -> Display -> [Raw.Command] -> [CommandResult]
    go _ctx _env _names [] = []
    go ctx env names (command : commands') = case command of

      Raw.CommandCompute _loc rawTerm ->
        let term = toTerm ctx env rawTerm
         in case infer ctx term of
              Left err  -> Failed err : rest
              Right _ty ->
                Computed (display names (nf (ctxScope ctx) (ctxDefs ctx) term)) : rest

      Raw.CommandCheck _loc rawTerm rawType ->
        let term = toTerm ctx env rawTerm
            ty = toTerm ctx env rawType
         in case check ctx ty universe >> check ctx term ty of
              Left err -> Failed err : rest
              Right () -> Checked (display names term) (display names ty) : rest

      Raw.CommandDef _loc name rawType rawValue ->
        let ty = toTerm ctx env rawType
            value = toTerm ctx env rawValue
         in case check ctx ty universe >> check ctx value ty of
              Left err -> Failed err : rest
              Right () ->
                Defined (prettyVarIdent name) :
                  withDefinition ctx ty value (\ctx' name' ->
                    go ctx'
                      (Map.insert name name' (Foil.sinkContainer env))
                      (Map.insert (Foil.nameId name') name names)
                      commands')
      where
        rest = go ctx env names commands'
        universe = Universe Raw.BNFC'NoPosition

-- | Show a raw identifier as it was written.
prettyVarIdent :: Raw.VarIdent -> String
prettyVarIdent (Raw.VarIdent x) = x

-- | Parse and interpret a program.
interpret :: String -> Either String [CommandResult]
interpret input = interpretProgram <$> parseProgram input

-- | Read a program on standard input, interpret it, and exit non-zero if any
-- command failed.
defaultMain :: IO ()
defaultMain = do
  input <- getContents
  case interpret input of
    Left err -> do
      putStrLn err
      exitFailure
    Right results -> do
      mapM_ (putStrLn . renderResult) results
      if succeeded results then return () else exitFailure
