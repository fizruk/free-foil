{-# LANGUAGE TemplateHaskell #-}
-- | Derive the 'Binary' instance a client's pattern (binder) type needs,
-- alongside the hand-written instances of "Control.Monad.Free.Foil.Binary".
--
-- A pattern type is a GADT over two scope indices, so its instance cannot
-- come from "GHC.Generics". What the deriver writes is the shape one would
-- write by hand: one tag byte per constructor in declaration order, then
-- the fields in order. Decoding happens /at the diagonal/, with every
-- scope index of a constructor instantiated to the same variable, which any
-- chain of binder indices admits. A single coercion then moves the result to
-- the requested indices. That coercion mints scope evidence, so a derived
-- instance is part of the same trust boundary as the library's own. See the
-- module documentation of "Control.Monad.Free.Foil.Binary".
module Control.Monad.Free.Foil.Binary.TH (deriveBinaryPattern) where

import           Control.Monad       (unless, zipWithM)
import           Data.Binary         (Binary (..))
import           Data.Binary.Get     (Get, getWord8)
import           Data.Binary.Put     (putWord8)
import qualified Data.Map            as Map
import           Language.Haskell.TH
import           Unsafe.Coerce       (unsafeCoerce)

-- | @'deriveBinaryPattern' ''Pattern@ writes
-- @instance (Binary p1, …) => Binary (Pattern p1 … n l)@ for a pattern
-- type of kind @… -> S -> S -> Type@ whose fields are parameters, name
-- binders, or nested patterns.
deriveBinaryPattern :: Name -> Q [Dec]
deriveBinaryPattern tyName = do
  info <- reify tyName
  (tvs, cons) <- case info of
    TyConI (DataD _ _ tvs _ cons _)    -> pure (tvs, cons)
    TyConI (NewtypeD _ _ tvs _ con _)  -> pure (tvs, [con])
    _ -> fail ("deriveBinaryPattern: " <> show tyName <> " is not a data type")
  unless (length tvs >= 2) $
    fail "deriveBinaryPattern: expected a type of kind ... -> S -> S -> Type"
  params <- mapM (\i -> newName ("p" <> show (i :: Int))) [1 .. length tvs - 2]
  nVar <- newName "n"
  lVar <- newName "l"
  ctors <- concat <$> mapM flatten cons
  unless (length ctors <= 256) $
    fail "deriveBinaryPattern: more than 256 constructors"
  putClauses <- zipWithM (putClause) [0 ..] ctors
  getMatches <- zipWithM (getMatch params nVar) [0 ..] ctors
  tagName <- newName "tag"
  let headTy = foldl AppT (ConT tyName) (map VarT (params <> [nVar, lVar]))
      context = [AppT (ConT ''Binary) (VarT p) | p <- params]
      failMatch = Match WildP
        (NormalB (AppE (VarE 'fail) (LitE (StringL "unknown pattern tag")))) []
      getBody = InfixE (Just (VarE 'getWord8)) (VarE '(>>=))
        (Just (LamE [VarP tagName]
          (CaseE (VarE tagName) (getMatches <> [failMatch]))))
  pure
    [ InstanceD Nothing context (AppT (ConT ''Binary) headTy)
        [ FunD 'put putClauses
        , ValD (VarP 'get) (NormalB getBody) []
        ]
    ]
  where
    flatten (ForallC _ _ con)   = flatten con
    flatten (GadtC names bts t) = pure [(c, map snd bts, t) | c <- names]
    flatten _ =
      fail "deriveBinaryPattern: expected GADT constructors (a pattern's indices vary per constructor)"

    putClause tag (cname, fields, _) = do
      args <- mapM (\i -> newName ("x" <> show (i :: Int))) [1 .. length fields]
      let puts = AppE (VarE 'putWord8) (LitE (IntegerL tag))
                   : [AppE (VarE 'put) (VarE a) | a <- args]
      pure (Clause [ConP cname [] (map VarP args)]
                   (NormalB (AppE (VarE 'mconcat) (ListE puts))) [])

    -- Decode at the diagonal: the constructor's own scope variables (the
    -- result indices and any intermediates) all become @n@, and its
    -- parameter variables become the instance's parameters. The chain of a
    -- pattern's indices always admits the diagonal. Each field's 'get' is
    -- annotated with the substituted type, pinning the intermediates.
    getMatch params nVar tag (cname, fields, result) = do
      let (_, resultArgs) = unfoldApps result
          paramPairs =
            [ (v, VarT p)
            | (VarT v, p) <- zip (take (length params) resultArgs) params ]
          subst = Map.fromList paramPairs
          substTy t = case t of
            VarT v    -> Map.findWithDefault (VarT nVar) v subst
            AppT f x  -> AppT (substTy f) (substTy x)
            SigT x k  -> SigT (substTy x) k
            ParensT x -> ParensT (substTy x)
            _         -> t
          getField ft = SigE (VarE 'get) (AppT (ConT ''Get) (substTy ft))
          chain = case fields of
            [] -> AppE (VarE 'pure) (ConE cname)
            (f : fs) -> foldl
              (\acc ft -> InfixE (Just acc) (VarE '(<*>)) (Just (getField ft)))
              (InfixE (Just (ConE cname)) (VarE '(<$>)) (Just (getField f)))
              fs
          diagTy = AppT (ConT ''Get) (substTy result)
          body = AppE (AppE (VarE 'fmap) (VarE 'unsafeCoerce)) (SigE chain diagTy)
      pure (Match (LitP (IntegerL tag)) (NormalB body) [])

    unfoldApps = go []
      where
        go args (AppT f x) = go (x : args) f
        go args t          = (t, args)
