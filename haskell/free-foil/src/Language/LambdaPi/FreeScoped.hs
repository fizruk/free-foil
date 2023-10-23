module Language.LambdaPi.FreeScoped where

data TermF scope term
  = LamF scope
  | AppF term term
  | PiF term scope
  deriving (Show)

-- FIXME: to be completed
