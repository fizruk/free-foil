module Language.LambdaPi.Foil where

import qualified Data.StringMap as SM

type Ident = String
type RawName = Ident
type RawScope = [Ident]

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

rawMember :: RawName −> RawScope −> Bool
rawMember (RawName i) (RawScope s) = elem i s

member :: Name l −> Scope n −> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarEE :: Name n -> Expr n
  AppEE :: Expr n -> Expr n -> Expr n
  LamEE :: NameBinder n l -> Expr l -> Expr n

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
class ExtEndo (n:: S)

class (ExtEndo n => ExtEndo l ) => Ext (n:: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

class Distinct (n :: S)
instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
withFresh :: Distinct n => Scope n
  −> (forall l . DExt n l => NameBinder n l −> r ) −> r
withFresh scope cont = withFreshBinder scope \ binder −>
  unsafeAssertFresh binder cont

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  −> (DExt n' l' => NameBinder n' l' −> r) −> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct −> case unsafeExt @n' @l' of
      Ext −> cont (unsafeCoerce binder)

data DistinctEvidence ( n:: S) where
Distinct :: Distinct n => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence ( n:: S) ( l :: S) where
Ext :: Ext n l => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withRefreshed :: Distinct o => Scope o −> Name i
  −> (forall o'. DExt o o' => NameBinder o o' −> r) −> r
withRefreshed scope name cont = if member name scope
  then withFresh scope cont
  else unsafeAssertFresh (UnsafeBinder name) cont

-- generic sinking
concreteSink :: DExt n l => Expr n −> Expr l
concreteSink = unsafeCoerce

class Sinkable (e :: S −> ∗) where
  sinkabilityProof :: (Name n −> Name l) −> e n −> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n −> e l
sink = unsafeCoerce

-- Substitution
data Substitution (ex::S -> *) (in::S) (out::S) = UnsafeSubstitution (forall n. Name n -> ex n) (SM.StringMap (e o))

lookupSusbst :: Substitution ex in out -> Name in -> ex out
lookupSusbst (UnsafeSubstitution f env) (UnsafeName (RawName name)) =
    case SM.lookup name env of
        Just ex -> ex
        Nothing -> f (UnsafeName (RawName name))

identitySubst :: (forall n. Name n -> e n) -> Substitution ex in in
identitySubst f = UnsafeSubstitution f SM.empty

addSubst :: Substitution ex in out -> NameBinder in in' -> ex out -> Substitution ex in' out
addSubst (UnsafeSubstitution f env) (UnsafeNameBinder (UnsafeName RawName name)) ex = UnsafeSubstitution f (SM.insert name ex env)

addRename :: Substitution ex in out -> NameBinder in in' -> Name out -> Substitution ex in' out
addRename s@(UnsafeSubstitution f env) b@(UnsafeBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution f env
    | otherwise = addSubst s b (f n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution f env) =
    UnsafeSubstitution f (fmap (sinkabilityProof rename) env)


-- Substitute part
substitute :: Distinct out => Scope out -> Substitution Expr in out -> Expr in -> Expr out
substitute scope subst = \case
    VarE name -> lookupSusbst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) (\binder` ->
        let subst' = addRename (sink subst) binder (nameOf binder`)
            scope' = extendScope binder' scope
            body' = substitute scope' subst' body' in LamE binder' body'
        )

toFoilTerm :: (Distinct n) => Term -> Scope n -> SM (Name n) -> Expr n
toFoilTerm scope env (App a b) = AppE (toFoilTerm env scope a) (toFoilTerm env scope b)
toFoilTerm scope env (Lam str body) = withFresh scope (\ s ->
  let scope' = extendScope s scope
      env' = SM.insert str (nameOf s) (fmap sink env) in LamE s (toFoilTerm scope' env' body)
toFoilTerm scope env (Var str) -> case SM.lookup str env of
  Just name −> VarE name
  Nothing -> error ("Unbound variable " ++ str )
-- Nothing −> withFresh scope  (\ s -> VarE (sink (nameOf s))) - is allowed? pbb not
toFoilTerm scope env (Pi _ _ _) = error ("Not yet implemented")
  -- Nothing −> withFresh scope  (\ s -> VarE (sink (nameOf s))) - is allowed? pbb not

whnf :: (Distinct l) => Scope n -> Expr n -> Expr l
whnf scope = \case
  AppE f arg ->
    case whnf scope f of
      LamE z body ->
        let scope' = extendScope z scope
        let subst = UnsafeSubstitution Var (SM.insert (nameOf z) arg empty)
        in substitute scope' subst body
      f' -> AppE f' arg
  t -> t

-- | Interpret a λΠ command.
interpretCommand :: Command -> IO ()
interpretCommand (CommandCompute term type_) =
      putStrLn ("  ↦ " ++ ppExpr (whnf emptyScope (toFoilTerm term)))
interpretCommand (CommandCompute term type_) =
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