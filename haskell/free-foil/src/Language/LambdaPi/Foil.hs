{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.LambdaPi.Foil where

import Data.Map (Map)
import qualified Data.Map as Map
import Language.LambdaPi.Simple.Abs
import Language.LambdaPi.Simple.Lex (tokens)
import Language.LambdaPi.Simple.Layout (resolveLayout)
import Language.LambdaPi.Simple.Par (pProgram)
import Language.LambdaPi.Simple.Print (printTree)

type Id = String
type RawName = Id
type RawScope = [Id]

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

data Scope (n :: S) = UnsafeScope RawScope
data Name (n :: S) = UnsafeName RawName
data NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)

ppName :: Name n -> String
ppName (UnsafeName name) = name

-- UnsafeName "z" :: Name ["x", "y", "z"]
-- UnsafeNameBinder (UnsafeName "z")
--   :: NameBinder ["x"] ["x", "y", "z"]

emptyScope :: Scope VoidS
emptyScope = UnsafeScope []

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName name)) (UnsafeScope scope) =
  UnsafeScope (name : scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope = head {- DO NOT WRITE LIKE ME -}
  [ name
  | n <- [1..]
  , let name = "x" <> show n
  , name `notElem` scope
  ]

withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember i s = elem i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: Name n -> Expr n
  AppE :: Expr n -> Expr n -> Expr n
  LamE :: NameBinder n l -> Expr l -> Expr n

-- >>> putStrLn $ ppExpr identity
-- λx1. x1
-- >>> putStrLn $ ppExpr two
-- λx1. λx2. x1(x1(x2))
ppExpr :: Expr n -> String
ppExpr expr = case expr of
  VarE name -> ppName name
  AppE e1 e2 -> ppExpr e1 ++ "(" ++ ppExpr e2 ++ ")"
  LamE x body -> "λ" ++ ppName (nameOf x) ++ ". " ++ ppExpr body


-- Distinct constraints
class ExtEndo (n :: S)

class (ExtEndo n => ExtEndo l ) => Ext (n:: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

class Distinct (n :: S)
instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
data DistinctEvidence ( n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence ( n:: S) ( l :: S) where
  Ext :: Ext n l => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withFresh :: Distinct n => Scope n
  -> (forall l . DExt n l => NameBinder n l -> r ) -> r
withFresh scope cont = withFreshBinder scope (\binder ->
  unsafeAssertFresh binder cont)

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    -- #FIXME: when using originally @l' and @n' gives an error about type variables not in scope
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed :: Distinct o => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope name cont = if member name scope
  then withFresh scope cont
  else unsafeAssertFresh (UnsafeNameBinder name) cont

-- generic sinking
concreteSink :: DExt n l => Expr n -> Expr l
concreteSink = unsafeCoerce

class Sinkable (e :: S -> *) where
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

-- Substitution
data Substitution (e :: S -> *) (i :: S) (o :: S) = UnsafeSubstitution (forall n. Name n -> e n) (Map String (e o))

lookupSusbst :: Substitution e i o -> Name i -> e o
lookupSusbst (UnsafeSubstitution f env) (UnsafeName name) =
    case Map.lookup name env of
        Just ex -> ex
        Nothing -> f (UnsafeName name)

identitySubst :: (forall n. Name n -> e n) -> Substitution e i i
identitySubst f = UnsafeSubstitution f Map.empty

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName name)) ex = UnsafeSubstitution f (Map.insert name ex env)

addRename :: Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename s@(UnsafeSubstitution f env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f env
    | otherwise = addSubst s b (f n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)


-- Substitute part
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSusbst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) (\binder' ->
        let subst' = addRename (sink subst) binder (nameOf binder')
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body in LamE binder' body'
        )

toFoilTerm :: (Distinct n) => Term -> Scope n -> Map String (Name n) -> Expr n
toFoilTerm (App a b) scope env = AppE (toFoilTerm a scope env) (toFoilTerm a scope env)
toFoilTerm (Lam str body) scope env = withFresh scope (\s ->
  let scope' = extendScope s scope
      env' = Map.insert str (nameOf s) (fmap sink env) in LamE s (toFoilTerm body scope' env'))
toFoilTerm (Var str) scope env = case Map.lookup str env of
  Just name -> VarE name
  Nothing -> error ("Unbound variable " ++ str)
-- #TODO: suppori Pi expressions
toFoilTerm (Pi _ _ _) scope env = error ("Not yet implemented")

whnf :: (Distinct l) => Scope n -> Expr n -> Expr l
whnf scope = \case
  AppE f arg ->
    case whnf scope f of
      LamE z body ->
        let scope' = extendScope z scope
            subst = UnsafeSubstitution VarE (Map.insert (nameOf z) arg Map.empty)
        in substitute scope' subst body
      f' -> AppE f' (sink arg)
  t -> sink t

-- | Interpret a λΠ command.
interpretCommand :: Command -> IO ()
interpretCommand (CommandCompute term type_) =
      putStrLn ("  ↦ " ++ ppExpr (whnf emptyScope (toFoilTerm term)))
-- #TODO: add typeCheck
interpretCommand (CommandCheck term type_) =
      putStrLn ("Not yet implemented")

-- | Interpret a λΠ program.
interpretProgram :: Program -> IO ()
interpretProgram (AProgram typedTerms) = mapM_ interpretCommand typedTerms

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