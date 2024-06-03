-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.LambdaPi.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pCommand
  , pListCommand
  , pTerm
  , pTerm1
  , pTerm2
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.LambdaPi.Syntax.Abs
import Language.LambdaPi.Syntax.Lex

}

%name pProgram Program
%name pCommand Command
%name pListCommand ListCommand
%name pTerm Term
%name pTerm1 Term1
%name pTerm2 Term2
%name pScopedTerm ScopedTerm
%name pPattern Pattern
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '('        { PT _ (TS _ 1)        }
  ')'        { PT _ (TS _ 2)        }
  ','        { PT _ (TS _ 3)        }
  '.'        { PT _ (TS _ 4)        }
  ':'        { PT _ (TS _ 5)        }
  ';'        { PT _ (TS _ 6)        }
  '_'        { PT _ (TS _ 7)        }
  'check'    { PT _ (TS _ 8)        }
  'compute'  { PT _ (TS _ 9)        }
  '×'        { PT _ (TS _ 10)       }
  'Π'        { PT _ (TS _ 11)       }
  'λ'        { PT _ (TS _ 12)       }
  'π₁'       { PT _ (TS _ 13)       }
  'π₂'       { PT _ (TS _ 14)       }
  '→'        { PT _ (TS _ 15)       }
  '𝕌'        { PT _ (TS _ 16)       }
  L_VarIdent { PT _ (T_VarIdent $$) }

%%

VarIdent :: { Language.LambdaPi.Syntax.Abs.VarIdent }
VarIdent  : L_VarIdent { Language.LambdaPi.Syntax.Abs.VarIdent $1 }

Program :: { Language.LambdaPi.Syntax.Abs.Program }
Program : ListCommand { Language.LambdaPi.Syntax.Abs.AProgram $1 }

Command :: { Language.LambdaPi.Syntax.Abs.Command }
Command
  : 'check' Term ':' Term { Language.LambdaPi.Syntax.Abs.CommandCheck $2 $4 }
  | 'compute' Term ':' Term { Language.LambdaPi.Syntax.Abs.CommandCompute $2 $4 }

ListCommand :: { [Language.LambdaPi.Syntax.Abs.Command] }
ListCommand
  : {- empty -} { [] } | Command ';' ListCommand { (:) $1 $3 }

Term :: { Language.LambdaPi.Syntax.Abs.Term }
Term
  : 'λ' Pattern '.' ScopedTerm { Language.LambdaPi.Syntax.Abs.Lam $2 $4 }
  | 'Π' '(' Pattern ':' Term ')' '→' ScopedTerm { Language.LambdaPi.Syntax.Abs.Pi $3 $5 $8 }
  | Term1 '×' Term1 { Language.LambdaPi.Syntax.Abs.Product $1 $3 }
  | '(' Term ',' Term ')' { Language.LambdaPi.Syntax.Abs.Pair $2 $4 }
  | 'π₁' '(' Term ')' { Language.LambdaPi.Syntax.Abs.First $3 }
  | 'π₂' '(' Term ')' { Language.LambdaPi.Syntax.Abs.Second $3 }
  | '𝕌' { Language.LambdaPi.Syntax.Abs.Universe }
  | Term1 { $1 }

Term1 :: { Language.LambdaPi.Syntax.Abs.Term }
Term1
  : Term1 Term2 { Language.LambdaPi.Syntax.Abs.App $1 $2 }
  | Term2 { $1 }

Term2 :: { Language.LambdaPi.Syntax.Abs.Term }
Term2
  : VarIdent { Language.LambdaPi.Syntax.Abs.Var $1 }
  | '(' Term ')' { $2 }

ScopedTerm :: { Language.LambdaPi.Syntax.Abs.ScopedTerm }
ScopedTerm : Term { Language.LambdaPi.Syntax.Abs.AScopedTerm $1 }

Pattern :: { Language.LambdaPi.Syntax.Abs.Pattern }
Pattern
  : '_' { Language.LambdaPi.Syntax.Abs.PatternWildcard }
  | VarIdent { Language.LambdaPi.Syntax.Abs.PatternVar $1 }
  | '(' Pattern ',' Pattern ')' { Language.LambdaPi.Syntax.Abs.PatternPair $2 $4 }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

}
