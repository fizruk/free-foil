{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Control.Monad.Foil.TH.MkInstancesFoil where

import           Language.Haskell.TH

import qualified Control.Monad.Foil         as Foil
import           Control.Monad.Foil.TH.Util
import           Data.List                  (nub)

-- | Generate 'Foil.Sinkable' and 'Foil.CoSinkable' instances.
mkInstancesFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkInstancesFoil termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name scopeTVars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name termTVars _kind termCons _deriv) <- reify termT

  coSinkablePatternD <- deriveCoSinkable nameT patternT

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

-- | Generate 'Foil.Sinkable' and 'Foil.CoSinkable' instances.
deriveCoSinkable
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
deriveCoSinkable nameT patternT = do
  TyConI (DataD _ctx _name patternTVars _kind patternCons _deriv) <- reify patternT

  return
    [ InstanceD Nothing [] (AppT (ConT ''Foil.CoSinkable) (PeelConT foilPatternT (map (VarT . tvarName) patternTVars)))
        [ FunD 'Foil.coSinkabilityProof (map clausePattern patternCons)
        , FunD 'Foil.withPattern (map clauseWithPattern patternCons) ]
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

        go _i _scope' rename' p [] = AppE (AppE (VarE cont) rename') p
        go i scope' rename' p ((_bang, PeelConT tyName _tyParams) : conParams)
          | tyName == nameT || tyName == patternT =
              AppE
                (foldl AppE (VarE 'Foil.withPattern) [VarE withNameBinder, VarE id', VarE comp, VarE scope', VarE xi])
                (LamE [VarP renamei, VarP xi']
                  (LetE [ValD (VarP scopei) (NormalB (AppE (AppE (VarE 'Foil.extendScopePattern) (VarE xi')) (VarE scope'))) []]
                    (go (i + 1) scopei (foldl AppE (VarE comp) [rename', VarE renamei]) (AppE p (VarE xi')) conParams)))
          where
            xi = mkName ("x" ++ show i)
            xi' = mkName ("x" ++ show i ++ "'")
            renamei = mkName ("f" ++ show i)
            scopei = mkName ("_scope" ++ show i)
        go i scope' rename' p (_ : conPatterns) =
          go (i + 1) scope' rename' (AppE p (VarE xi)) conPatterns
          where
            xi = mkName ("x" ++ show i)

-- | Generate 'Foil.Sinkable' and 'Foil.CoSinkable' instances.
deriveUnifiablePattern
  :: Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
deriveUnifiablePattern nameT patternT = do
  TyConI (DataD _ctx _name patternTVars _kind patternCons _deriv) <- reify patternT

  let (eqTypes, clauses) = mapM clauseUnifyPatterns patternCons
      ctx = nub [ AppT (ConT ''Foil.UnifiableInPattern) type_ | type_ <- eqTypes, type_ `elem` map (VarT . tvarName) patternTVars ]
  return
    [ InstanceD Nothing ctx (AppT (ConT ''Foil.UnifiablePattern) (PeelConT foilPatternT (map (VarT . tvarName) patternTVars)))
        [ FunD 'Foil.unifyPatterns (clauses ++ [notUnifiableClause]) ]
    ]

  where
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

    notUnifiableClause :: Clause
    notUnifiableClause = Clause [WildP, WildP] (NormalB (ConE 'Foil.NotUnifiable)) []

    clauseUnifyPatterns :: Con -> ([Type], Clause)
    clauseUnifyPatterns RecC{} = error "Record constructors (RecC) are not supported yet!"
    clauseUnifyPatterns InfixC{} = error "Infix constructors (InfixC) are not supported yet!"
    clauseUnifyPatterns ForallC{} = error "Existential constructors (ForallC) are not supported yet!"
    clauseUnifyPatterns GadtC{} = error "GADT constructors (GadtC) are not supported yet!"
    clauseUnifyPatterns RecGadtC{} = error "Record GADT constructors (RecGadtC) are not supported yet!"
    clauseUnifyPatterns (NormalC conName params) =
      case go 1 [] [] params of
        (body, eqTypes) ->
          (eqTypes, Clause
            [ConP foilConName [] paramsL, ConP foilConName [] paramsR]
            (NormalB body)
            [])
      where
        foilConName = mkName ("Foil" ++ nameBase conName)
        paramsL = zipWith (mkConParamPattern "l") params [1..]
        paramsR = zipWith (mkConParamPattern "r") params [1..]
        mkConParamPattern s _ i = VarP (mkName (s ++ show i))

        mkUnifyAllPairsRev [] = AppE (ConE 'Foil.SameNameBinders) (VarE 'Foil.emptyNameBinders)
        mkUnifyAllPairsRev [(isNameBinder, l, r)]
          | isNameBinder = AppE (AppE (VarE 'Foil.unifyNameBinders) l) r
          | otherwise    = AppE (AppE (VarE 'Foil.unifyPatterns) l) r
        mkUnifyAllPairsRev ((isNameBinder, l, r) : pairs) =
          InfixE
            (Just (mkUnifyAllPairsRev pairs))
            (VarE (if isNameBinder then 'Foil.andThenUnifyNameBinders else 'Foil.andThenUnifyPatterns))
            (Just (TupE [Just l, Just r]))


        go _i eqTypes pairsRev [] = (mkUnifyAllPairsRev pairsRev, eqTypes)
        go i eqTypes pairsRev ((_bang, PeelConT tyName _tyParams) : conParams)
          | tyName == nameT || tyName == patternT =
            case go (i + 1) eqTypes ((isNameBinder, l, r) : pairsRev) conParams of
              (next, eqTypes') ->
                (CaseE (TupE [Just (AppE (VarE 'Foil.assertDistinct) l), Just (AppE (VarE 'Foil.assertDistinct) r)])
                  [Match
                    (TupP [ConP 'Foil.Distinct [] [], ConP 'Foil.Distinct [] []])
                    (NormalB next)
                    []], eqTypes')
          where
            isNameBinder = tyName == nameT
            l = VarE (mkName ("l" ++ show i))
            r = VarE (mkName ("r" ++ show i))
        go i eqTypes pairsRev ((_bang, type_) : conPatterns) =
          case go (i + 1) eqTypes pairsRev conPatterns of
            (next, eqTypes') ->
              (CondE
                (InfixE (Just l) (VarE 'Foil.unifyInPattern) (Just r))
                next
                (ConE 'Foil.NotUnifiable), type_ : eqTypes')
          where
            l = VarE (mkName ("l" ++ show i))
            r = VarE (mkName ("r" ++ show i))
