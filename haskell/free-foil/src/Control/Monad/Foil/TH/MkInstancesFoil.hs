{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Control.Monad.Foil.TH.MkInstancesFoil (mkInstancesFoil) where

import           Language.Haskell.TH

import qualified Control.Monad.Foil  as Foil

-- | Generate 'Foil.Sinkable' and 'Foil.CoSinkable' instances.
mkInstancesFoil
  :: Name -- ^ Type name for raw terms.
  -> Name -- ^ Type name for raw variable identifiers.
  -> Name -- ^ Type name for raw scoped terms.
  -> Name -- ^ Type name for raw patterns.
  -> Q [Dec]
mkInstancesFoil termT nameT scopeT patternT = do
  TyConI (DataD _ctx _name _tvars _kind patternCons _deriv) <- reify patternT
  TyConI (DataD _ctx _name _tvars _kind scopeCons _deriv) <- reify scopeT
  TyConI (DataD _ctx _name _tvars _kind termCons _deriv) <- reify termT

  return
    [ InstanceD Nothing [] (AppT (ConT ''Foil.Sinkable) (ConT foilScopeT))
        [ FunD 'Foil.sinkabilityProof (map clauseScopedTerm scopeCons) ]

    , InstanceD Nothing [] (AppT (ConT ''Foil.CoSinkable) (ConT foilPatternT))
        [ FunD 'Foil.coSinkabilityProof (map clausePattern patternCons) ]

    , InstanceD Nothing [] (AppT (ConT ''Foil.Sinkable) (ConT foilTermT))
        [ FunD 'Foil.sinkabilityProof (map clauseTerm termCons)]
    ]

  where
    foilTermT = mkName ("Foil" ++ nameBase termT)
    foilScopeT = mkName ("Foil" ++ nameBase scopeT)
    foilPatternT = mkName ("Foil" ++ nameBase patternT)

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
        rename = mkName "rename"
        conParamPatterns = zipWith mkConParamPattern params [1..]
        mkConParamPattern _ i = VarP (mkName ("x" ++ show i))

        go _i _rename' p [] = p
        go i rename' p ((_bang, ConT tyName) : conParams)
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
        go i rename' p ((_bang, ConT tyName) : conParams)
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
