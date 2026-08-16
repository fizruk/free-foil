{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Module parameters as a labelled telescope, and closing a declaration over
-- the parameters it uses.
--
-- The telescope itself — the type, its pattern instances, and the dependency
-- closure — lives in the library ("Control.Monad.Foil.Telescope"), where it
-- moved after being proven here. What stays in the demo is the
-- instantiation: labels are spellings, payloads are types, and 'discharge'
-- folds the closed type into @Π@s and the value into @λ@s.
--
-- A parametrised module
--
-- > module Group (A : 𝕌) (m : A → A → A) ;
-- > def twice : A → A := λ x ⇒ m x x
--
-- checks every declaration with its parameters in scope, and then closes each
-- one over exactly the parameters that declaration turns out to use, so that
-- what leaves the module is an ordinary closed definition
-- @Group.twice : Π (A : 𝕌) → Π (m : A → A → A) → A → A@. A declaration that
-- uses no parameter is closed over nothing and stays a plain constant. An
-- optional @over (…)@ clause states that set in the source, and is checked
-- against the computed one by 'checkDischarge'.
--
-- == Where the scope restriction is
--
-- This is the place the demo needs free-foil\'s scope /restriction/ rather than
-- its extension. Checking happens in the scope @p@ that the parameters extend
-- the module\'s scope @n@ to; the result has to come back to @n@, because @n@ is
-- where the module\'s exports live and where the next module starts.
--
-- It is done in three steps, and the point of the arrangement is that the term
-- is walked a fixed number of times rather than once per parameter:
--
-- 1. 'supportOf' the type and the value, once each.
-- 2. 'Foil.closeOverTelescope' closes that set under the parameter types.
--    Keeping @(x : A)@ puts @A@ into the result, so @A@ has to be kept as
--    well. One pass from the inside out is enough, since a parameter\'s type
--    mentions only the parameters before it.
-- 3. 'Foil.withThinnedNameBinderList' cuts the chain of binders down to that
--    set in one step, and 'discharge' rebuilds the abstractions along the
--    thinned chain, restricting each parameter type and the body into it.
--
-- The alternative, asking 'unsinkAST' at every parameter whether the term can
-- do without it, is shorter to write and walks the whole term once per
-- parameter.
module Language.MLTT.Telescope (
  module Control.Monad.Foil.Telescope,
  ParamTelescope,
  Discharged (..),
  discharge,
  checkDischarge,
) where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Foil.Telescope
import           Control.Monad.Free.Foil      (supportOf, unsinkAST)
import           Data.List                    (intercalate, sort)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve        (prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs     as Raw

-- | A module\'s parameters: the labels are spellings, the payloads are types.
type ParamTelescope a = Telescope Raw.VarIdent (Term' a)

-- | A declaration after being closed over the module's parameters.
data Discharged a n = Discharged
  { dischargedType  :: Term' a n
    -- ^ The type, wrapped in a @Π@ for each parameter kept.
  , dischargedValue :: Term' a n
    -- ^ The value, wrapped in a @λ@ for each parameter kept.
  , dischargedOver  :: [Raw.VarIdent]
    -- ^ Which parameters those were, outermost first.
  }

-- | Close a checked declaration over a given set of the module's parameters.
--
-- The type and the value are closed over together, over the same parameters,
-- since @f : T@ and @f := v@ have to stay a matching pair: if only the value
-- mentions a parameter, the type still gains a (non-dependent) @Π@ for it.
--
-- Given 'Nothing', the set is the computed one and the result is a 'Right'.
-- Given a /declared/ set, 'Left' names the parameters the declaration needs and
-- that set does not have, which is the useful thing to say about a wrong
-- @over@ clause.
discharge
  :: forall a n l. (Foil.Distinct n, Foil.Distinct l)
  => a                        -- ^ The position to put on the abstractions introduced.
  -> Foil.Scope n             -- ^ The module's scope, which the result lives in.
  -> ParamTelescope a n l
  -> Maybe (Foil.NameSet l)   -- ^ A declared set of parameters, if there is one.
  -> Term' a l                -- ^ The declaration's type, checked with parameters in scope.
  -> Term' a l                -- ^ Its value, likewise.
  -> Either [Raw.VarIdent] (Discharged a n)
discharge loc scope tele declared ty value
  | not (null missing) = Left missing
  | otherwise =
      Foil.withThinnedNameBinderList keep (telescopeBinders tele) $
        \(thinned :: Foil.NameBinderList n m) ->
          let scopeM = Foil.extendScopePattern thinned scope
           in case (unsinkAST scopeM ty, unsinkAST scopeM value,
                    traverse (\p -> (,) (paramLabel p) <$> unsinkAST scopeM (paramType p)) kept) of
                (Just tyM, Just valueM, Just paramsM) ->
                  build scope thinned paramsM tyM valueM
                -- Unreachable: 'keep' contains the support and is closed, which
                -- is what 'missing' being empty says.
                _ -> Left needs
  where
    params = telescopeParams tele

    -- The support of the declaration, closed under the parameter types. Two
    -- walks of the term, whatever the number of parameters.
    needed = closeOverTelescope supportOf params (supportOf ty <> supportOf value)

    keep = case declared of
      Nothing -> needed
      Just s  -> s
    kept = [p | p <- params, Foil.nameSetMember (paramName p) keep]

    -- A parameter the declaration needs and the set does not have. Testing this
    -- up front is what leaves 'build' with nothing to report: every restriction
    -- it performs is then into a scope that has what the term needs.
    missing =
      [ paramLabel p
      | p <- params
      , Foil.nameSetMember (paramName p) needed
      , not (Foil.nameSetMember (paramName p) keep)
      ]

    -- Every parameter the declaration needs, whether or not it is being kept.
    needs = [paramLabel p | p <- params, Foil.nameSetMember (paramName p) needed]

    -- Rebuild the abstractions along the thinned chain. Everything has already
    -- been restricted into the thinned scope @m@, so each step only has to take
    -- the parameter type one scope further out, and the evidence for that is
    -- the remaining chain.
    build
      :: forall m0 m. (Foil.Distinct m0, Foil.Distinct m)
      => Foil.Scope m0
      -> Foil.NameBinderList m0 m
      -> [(Raw.VarIdent, Term' a m)]
      -> Term' a m
      -> Term' a m
      -> Either [Raw.VarIdent] (Discharged a m0)
    build scope' binders paramsM tyM valueM = case (binders, paramsM) of
      (Foil.NameBinderListEmpty, _) -> Right (Discharged tyM valueM [])
      (Foil.NameBinderListCons binder rest, (name, paramTyM) : ps) ->
        case (Foil.assertExt binders, Foil.assertDistinct binder) of
          (Foil.Ext, Foil.Distinct) -> case unsinkAST scope' paramTyM of
            Nothing -> Left needs
            Just paramTy -> do
              inner <- build (Foil.extendScope binder scope') rest ps tyM valueM
              return Discharged
                { dischargedType  = Pi loc paramTy (PatternVar loc binder) (dischargedType inner)
                , dischargedValue = Lam loc (PatternVar loc binder) (dischargedValue inner)
                , dischargedOver  = name : dischargedOver inner
                }
      -- Unreachable: the chain and the parameters were filtered by one set.
      (Foil.NameBinderListCons _ _, []) -> Left needs

-- | Check a declared @over@ clause against the parameters actually kept.
--
-- The clause is optional, and it never changes what is defined: the computed
-- list is authoritative either way, so an accepted clause is one that agrees
-- with it. Both directions are reported, since listing a parameter that is not
-- used is as much a mistake in the documentation as omitting one that is.
--
-- It is spelled @over@ rather than @uses@ because rzk has a @uses@ clause that
-- is a different thing: mandatory, and listing the implicit assumptions of a
-- definition rather than the parameters of its module.
checkDischarge :: Raw.Discharge -> [Raw.VarIdent] -> Either String ()
checkDischarge (Raw.NoDischarge _loc) _ = Right ()
checkDischarge (Raw.DischargeOver _loc declared) over
  | sort declared == sort over = Right ()
  | otherwise = Left $ unlines
      [ "declared: over (" <> render declared <> ")"
      , "  actual: over (" <> render over <> ")" ]
  where
    -- The clause may be written in any order; the report gives telescope order.
    render = intercalate ", " . map prettyVarIdent
