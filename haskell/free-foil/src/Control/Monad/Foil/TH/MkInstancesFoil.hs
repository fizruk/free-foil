{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Control.Monad.Foil.TH.MkInstancesFoil (
  mkInstancesFoil,
  mkCoSinkableFoilPattern,
  deriveCoSinkable,
) where

import           Language.Haskell.TH

import qualified Control.Monad.Foil         as Foil
import           Control.Monad.Foil.TH.Util

-- | Generate 'Foil.Sinkable' and 'Foil.CoSinkable' instances.
--
-- @since 0.0.1
mkInstancesFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkInstancesFoil termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name scopeTVars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT

  coSinkablePatternD <- mkCoSinkableFoilPattern nameT patternT

  return $
    [ InstanceD Nothing [] (AppT (ConT ''Foil.Sinkable) (PeelConT foilScopeT (map (VarT . tvarName) scopeTVars)))
        [ FunD 'Foil.sinkabilityProof (map clauseScopedTerm scopeCons) ]

    , InstanceD Nothing [] (AppT (ConT ''Foil.Sinkable) (PeelConT foilTermT (map (VarT . tvarName) termTVars)))
        [ FunD 'Foil.sinkabilityProof (map clauseTerm termCons)]
    ] ++ coSinkablePatternD

  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)

    clauseScopedTerm :: Con -> Clause
    clauseScopedTerm = clauseTerm

    clauseTerm :: Con -> Clause
    clauseTerm RecC{} = error "Record constructors (RecC) are not supported yet!"
    clauseTerm InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
    clauseTerm ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
    clauseTerm GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
    clauseTerm RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"
    clauseTerm (NormalC conName params) =
      Clause
        [VarP rename, ConP foilConName [] conParamPatterns]
        (NormalB (go 1 (VarE rename) (ConE foilConName) params))
        []
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        rename = mkName "_rename"
        conParamPatterns = zipWith mkConParamPattern params [1..]
        mkConParamPattern _ i = VarP (mkName ("x" ++ show i))

        go _i _rename' p [] = p
        go i rename' p ((_bang, PeelConT tyName _tyParams) : conParams)
          | tyName == nameT =
              go (i + 1) rename' (AppE p (AppE (VarE rename) (VarE xi))) conParams
          | tyName == termT =
              go (i + 1) rename' (AppE p (AppE (AppE (VarE 'Foil.sinkabilityProof) (VarE rename)) (VarE xi))) conParams
          | tyName == scopeT =
              go (i + 1) rename' (AppE p (AppE (AppE (VarE 'Foil.sinkabilityProof) rename') (VarE xi))) conParams
          | tyName == patternT =
              AppE
                (AppE (AppE (VarE 'Foil.coSinkabilityProof) rename') (VarE xi))
                (LamE [VarP renamei, VarP xi']
                  (go (i + 1) (VarE renamei) (AppE p (VarE xi')) conParams))
          where
            xi = mkName ("x" ++ show i)
            xi' = mkName ("x" ++ show i ++ "'")
            renamei = mkName ("rename" ++ show i)
        go i rename' p (_ : conPatterns) =
          go (i + 1) rename' (AppE p (VarE xi)) conPatterns
          where
            xi = mkName ("x" ++ show i)

-- | Generate the 'Foil.CoSinkable' instance of the pattern type that
-- 'Control.Monad.Foil.TH.MkFoilData.mkFoilPattern' generates from a raw
-- pattern type, given the raw types of identifiers and patterns.
-- 'deriveCoSinkable' takes the scope-safe pattern type itself.
--
-- Up to 0.5.0, this was 'deriveCoSinkable'.
--
-- @since 0.6.0
mkCoSinkableFoilPattern
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkCoSinkableFoilPattern nameT patternT = do
  TyConI (DataD _ctx _name patternTVars _kind patternCons _deriv) <- reify patternT

  return
    [ InstanceD Nothing [] (AppT (ConT ''Foil.CoSinkable) (PeelConT foilPatternT (map (VarT . tvarName) patternTVars)))
        [ FunD 'Foil.coSinkabilityProof (map clausePattern patternCons)
        , FunD 'Foil.withPattern (map clauseWithPattern patternCons)
        , FunD 'Foil.nameBinderListOf (map clauseNameBinderListOf patternCons) ]
    ]

  where
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    clausePattern :: Con -> Clause
    clausePattern RecC{} = error "Record constructors (RecC) are not supported yet!"
    clausePattern InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
    clausePattern ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
    clausePattern GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
    clausePattern RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"
    clausePattern (NormalC conName params) =
      Clause
        [VarP rename, ConP foilConName [] conParamPatterns, VarP cont]
        (NormalB (go 1 (VarE rename) (ConE foilConName) params))
        []
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        rename = mkName "rename"
        cont = mkName "cont"
        conParamPatterns = zipWith mkConParamPattern params [1..]
        mkConParamPattern _ i = VarP (mkName ("x" ++ show i))

        go _i rename' p [] = AppE (AppE (VarE cont) rename') p
        go i rename' p ((_bang, PeelConT tyName _tyParams) : conParams)
          | tyName == nameT || tyName == patternT =
              AppE
                (AppE (AppE (VarE 'Foil.coSinkabilityProof) rename') (VarE xi))
                (LamE [VarP renamei, VarP xi']
                  (go (i + 1) (VarE renamei) (AppE p (VarE xi')) conParams))
          where
            xi = mkName ("x" ++ show i)
            xi' = mkName ("x" ++ show i ++ "'")
            renamei = mkName ("rename" ++ show i)
        go i rename' p (_ : conPatterns) =
          go (i + 1) rename' (AppE p (VarE xi)) conPatterns
          where
            xi = mkName ("x" ++ show i)

    -- The binders of the binding fields, in order, without going through
    -- 'Foil.withPattern'.
    clauseNameBinderListOf :: Con -> Clause
    clauseNameBinderListOf (NormalC conName params) =
      Clause [ConP foilConName [] conParamPatterns] (NormalB body) []
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        conParamPatterns = zipWith mkConParamPattern params [1 :: Int ..]
        mkConParamPattern (_bang, PeelConT tyName _)
          | tyName == nameT || tyName == patternT = VarP . xi
        mkConParamPattern _ = const WildP
        xi i = mkName ("x" ++ show i)
        binding =
          [ AppE (VarE 'Foil.nameBinderListOf) (VarE (xi i))
          | ((_bang, PeelConT tyName _), i) <- zip params [1 :: Int ..]
          , tyName == nameT || tyName == patternT ]
        body = case binding of
          [] -> ConE 'Foil.NameBinderListEmpty
          _  -> foldr1 (\l r -> foldl AppE (VarE 'Foil.concatNameBinderLists) [l, r]) binding
    clauseNameBinderListOf _ = error "Only normal constructors are supported here"

    clauseWithPattern :: Con -> Clause
    clauseWithPattern RecC{} = error "Record constructors (RecC) are not supported yet!"
    clauseWithPattern InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
    clauseWithPattern ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
    clauseWithPattern GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
    clauseWithPattern RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"
    clauseWithPattern (NormalC conName params) =
      Clause
        [VarP withNameBinder, VarP id', VarP comp, VarP scope, ConP foilConName [] conParamPatterns, VarP cont]
        (NormalB (go 1 scope (VarE id') (ConE foilConName) params))
        []
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        withNameBinder = mkName "_withNameBinder"
        id' = mkName "id'"
        comp = mkName "_comp"
        scope = mkName "_scope"
        cont = mkName "cont"
        conParamPatterns = zipWith mkConParamPattern params [1..]
        mkConParamPattern _ i = VarP (mkName ("x" ++ show i))

        go _i scope' rename' p [] = AppE (AppE (AppE (VarE cont) rename') p) (VarE scope')
        go i scope' rename' p ((_bang, PeelConT tyName _tyParams) : conParams)
          | tyName == nameT || tyName == patternT =
              AppE
                (foldl AppE (VarE 'Foil.withPattern) [VarE withNameBinder, VarE id', VarE comp, VarE scope', VarE xi])
                (LamE [VarP renamei, VarP xi', VarP scopei]
                  (go (i + 1) scopei (foldl AppE (VarE comp) [rename', VarE renamei]) (AppE p (VarE xi')) conParams))
          where
            xi = mkName ("x" ++ show i)
            xi' = mkName ("x" ++ show i ++ "'")
            renamei = mkName ("f" ++ show i)
            scopei = mkName ("scope" ++ show i)
        go i scope' rename' p (_ : conPatterns) =
          go (i + 1) scope' rename' (AppE p (VarE xi)) conPatterns
          where
            xi = mkName ("x" ++ show i)

-- | Generate the 'Foil.CoSinkable' instance of a scope-safe pattern type.
-- 'mkCoSinkableFoilPattern' takes the raw pattern type instead.
--
-- > data Pat (n :: S) (l :: S) where
-- >   PatVar  :: NameBinder n l -> Pat n l
-- >   PatPair :: NameBinder n i -> NameBinder i l -> Pat n l
-- >
-- > deriveCoSinkable ''Pat
--
-- A field is a 'Foil.NameBinder', a nested pattern, or a payload that
-- mentions no scope. A payload indexed by a scope needs a hand-written
-- instance (see 'Foil.transportPayload').
--
-- @since 0.6.0
deriveCoSinkable :: Name -> Q [Dec]
deriveCoSinkable patternT = do
  (tvars, cons) <- reify patternT >>= \case
    TyConI (DataD _ _ tvs _ cs _)    -> return (tvs, cs)
    TyConI (NewtypeD _ _ tvs _ c _)  -> return (tvs, [c])
    _ -> fail ("deriveCoSinkable: " ++ show patternT ++ " is not a data type")
  let params = map tvarName tvars
  if length params < 2
    then fail ("deriveCoSinkable: " ++ show patternT ++ " has fewer than two type parameters")
    else do
      fields <- concat <$> mapM (patternConFields patternT) cons
      coSinkClauses <- mapM patternCoSinkabilityProofClause fields
      withPatClauses <- mapM patternWithPatternClause fields
      listClauses <- mapM patternNameBinderListOfClause fields
      -- A pattern that nests itself has a recursive 'Foil.withPattern', which
      -- cannot inline.
      let recursive = or [ h == ConT patternT | (_, sorts) <- fields, PatternNested h <- sorts ]
          inline = [ PragmaD (InlineP 'Foil.withPattern Inline FunLike AllPhases) | not recursive ]
      return
        [ InstanceD Nothing [] (AppT (ConT ''Foil.CoSinkable) (foldl AppT (ConT patternT) (map VarT (take (length params - 2) params))))
            ([ FunD 'Foil.coSinkabilityProof coSinkClauses
             , FunD 'Foil.withPattern withPatClauses
             , FunD 'Foil.nameBinderListOf listClauses
             ] ++ inline)
        ]

-- | How a field of a pattern constructor takes part in its instance.
data PatternField
  = PatternBinder        -- ^ A 'Foil.NameBinder'.
  | PatternNested Type   -- ^ A nested pattern, with its own 'Foil.CoSinkable'; its type's head.
  | PatternPayload       -- ^ A field that mentions no scope.

-- | The constructors of a pattern type, each with the sorts of its fields.
-- The scopes of a constructor are the last two arguments of its return type
-- and its existential variables, such as the intermediate scope of a pair.
patternConFields :: Name -> Con -> Q [(Name, [PatternField])]
patternConFields patternT = go []
  where
    go bound = \case
      NormalC conName _ -> fail ("deriveCoSinkable: constructor " ++ show conName
        ++ " of " ++ show patternT ++ " is not in GADT syntax, so its scopes are unknown")
      RecC conName _ -> go bound (NormalC conName [])
      InfixC _ conName _ -> go bound (NormalC conName [])
      ForallC tvs _ con -> go (bound ++ map tvarName tvs) con
      RecGadtC conNames types retType -> go bound (GadtC conNames (map removeName types) retType)
      GadtC conNames types retType -> do
        let (_, args) = unApplyType retType
            scopes = [ v | VarT v <- drop (length args - 2) args ] ++ bound
        sorts <- mapM (fieldSort scopes . snd) types
        return [ (conName, sorts) | conName <- conNames ]

    fieldSort scopes type_ =
      let (headT, args) = unApplyType type_
          mentions = any (`elem` scopes) (namesOfType type_)
          lastTwoScopes = case reverse args of
            VarT b : VarT a : _ -> a `elem` scopes && b `elem` scopes
            _                   -> False
      in case headT of
           ConT n | n == ''Foil.NameBinder -> return PatternBinder
           _ | lastTwoScopes -> return (PatternNested headT)
             | not mentions  -> return PatternPayload
             | otherwise -> fail ("deriveCoSinkable: a field of type " ++ pprint type_
                 ++ " in " ++ show patternT ++ " mentions a scope; write the instance by hand"
                 ++ " (transportPayload is the sanctioned way to rebuild such a field)")

-- | A type split into its head and arguments, without parentheses and kind
-- signatures.
unApplyType :: Type -> (Type, [Type])
unApplyType = go []
  where
    go acc (AppT f x)   = go (x : acc) f
    go acc (ParensT t)  = go acc t
    go acc (SigT t _)   = go acc t
    go acc t            = (t, acc)

-- | The type variables a type mentions.
namesOfType :: Type -> [Name]
namesOfType = \case
  VarT v       -> [v]
  AppT f x     -> namesOfType f ++ namesOfType x
  SigT t _     -> namesOfType t
  ParensT t    -> namesOfType t
  AppKindT t _ -> namesOfType t
  _            -> []

isBindingField :: PatternField -> Bool
isBindingField = \case
  PatternPayload -> False
  _              -> True

-- | One 'Foil.coSinkabilityProof' clause: the binding fields are renamed in
-- turn, each with the renaming the previous one extended.
patternCoSinkabilityProofClause :: (Name, [PatternField]) -> Q Clause
patternCoSinkabilityProofClause (conName, sorts) = do
  rename <- newName (if any isBindingField sorts then "rename" else "_rename")
  cont <- newName "cont"
  xs <- mapM (\i -> newName ("x" ++ show i)) [1 .. length sorts]
  let go renameCur [] fields = return (VarE cont `AppE` VarE renameCur `AppE` foldl AppE (ConE conName) (fields []))
      go renameCur ((PatternPayload, x) : rest) fields = go renameCur rest (fields . (VarE x :))
      go renameCur ((_, x) : rest) fields = do
        renameNext <- newName "rename'"
        x' <- newName (nameBase x ++ "'")
        body <- go renameNext rest (fields . (VarE x' :))
        return (VarE 'Foil.coSinkabilityProof `AppE` VarE renameCur `AppE` VarE x
                  `AppE` LamE [VarP renameNext, VarP x'] body)
  body <- go rename (zip sorts xs) id
  return (Clause [VarP rename, ConP conName [] (map VarP xs), VarP cont] (NormalB body) [])

-- | One 'Foil.withPattern' clause, in the form of
-- 'Control.Monad.Free.Foil.TH.MkFreeFoil.mkFreeFoil': a binder field goes
-- through @withBinder@ and extends the scope for the fields to its right, a
-- nested pattern through its own 'Foil.withPattern', and the results compose
-- left to right.
patternWithPatternClause :: (Name, [PatternField]) -> Q Clause
patternWithPatternClause (conName, sorts) = do
  let nBinding = length (filter isBindingField sorts)
      hasNested = any (\case PatternNested _ -> True; _ -> False) sorts
      usedIf b n = if b then n else '_' : n
  withBinder <- newName (usedIf (nBinding > 0) "withBinder")
  unit_ <- newName (usedIf (nBinding == 0 || hasNested) "unit_")
  comp_ <- newName (usedIf (nBinding >= 2 || hasNested) "comp_")
  scope <- newName "scope"
  cont <- newName "cont"
  xs <- mapM (\i -> newName ("x" ++ show i)) [1 .. length sorts]
  let go scopeCur acc [] fields =
        return (VarE cont `AppE` maybe (VarE unit_) id acc
                  `AppE` foldl AppE (ConE conName) (fields [])
                  `AppE` VarE scopeCur)
      go scopeCur acc ((PatternPayload, x) : rest) fields = go scopeCur acc rest (fields . (VarE x :))
      go scopeCur acc ((sort_, x) : rest) fields = do
        x' <- newName (nameBase x ++ "'")
        f <- newName "f"
        scopeNext <- newName "scope'"
        let acc' = case acc of
              Nothing -> VarE f
              Just a  -> VarE comp_ `AppE` a `AppE` VarE f
        body <- go scopeNext (Just acc') rest (fields . (VarE x' :))
        return $ case sort_ of
          PatternBinder ->
            VarE withBinder `AppE` VarE scopeCur `AppE` VarE x
              `AppE` LamE [VarP f, VarP x']
                  (LetE [ValD (VarP scopeNext)
                           (NormalB (VarE 'Foil.extendScope `AppE` VarE x' `AppE` VarE scopeCur)) []]
                     body)
          _ ->
            VarE 'Foil.withPattern `AppE` VarE withBinder `AppE` VarE unit_
              `AppE` VarE comp_ `AppE` VarE scopeCur `AppE` VarE x
              `AppE` LamE [VarP f, VarP x', VarP scopeNext] body
  body <- go scope Nothing (zip sorts xs) id
  return (Clause
    [VarP withBinder, VarP unit_, VarP comp_, VarP scope, ConP conName [] (map VarP xs), VarP cont]
    (NormalB body) [])

-- | One 'Foil.nameBinderListOf' clause: the binding fields, left to right.
patternNameBinderListOfClause :: (Name, [PatternField]) -> Q Clause
patternNameBinderListOfClause (conName, sorts) = do
  xs <- mapM (\i -> newName ("x" ++ show i)) [1 .. length sorts]
  let pats = [ if isBindingField s then VarP x else WildP | (s, x) <- zip sorts xs ]
      -- A binder is consed on directly. Only a nested pattern's list is
      -- concatenated, since 'Foil.concatNameBinderLists' is recursive and
      -- copies its first argument.
      list = \case
        [] -> ConE 'Foil.NameBinderListEmpty
        [(PatternNested _, x)] -> VarE 'Foil.nameBinderListOf `AppE` VarE x
        (PatternNested _, x) : rest ->
          VarE 'Foil.concatNameBinderLists `AppE` (VarE 'Foil.nameBinderListOf `AppE` VarE x) `AppE` list rest
        (_, x) : rest -> ConE 'Foil.NameBinderListCons `AppE` VarE x `AppE` list rest
      body = list [ (s, x) | (s, x) <- zip sorts xs, isBindingField s ]
  return (Clause [ConP conName [] pats] (NormalB body) [])
