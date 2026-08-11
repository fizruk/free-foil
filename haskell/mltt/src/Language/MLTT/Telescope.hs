{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Module parameters, and discharging a declaration over the ones it uses.
--
-- A parametrised module
--
-- > module Group (A : 𝕌) (m : A → A → A) ;
-- > def twice : A → A := λ x ⇒ m x x
--
-- checks every declaration with its parameters in scope, and then /discharges/
-- each one over exactly the parameters that declaration turns out to use, so
-- that what leaves the module is an ordinary closed definition
-- @Group.twice : Π (A : 𝕌) → Π (m : A → A → A) → A → A@. A declaration that
-- uses no parameter is discharged over nothing and stays a plain constant. An
-- optional @over (…)@ clause states that set in the source, and is checked
-- against the computed one by 'checkDischarge'.
--
-- == Where the scope restriction is
--
-- Discharge is the place this demo needs free-foil's scope /restriction/ rather
-- than its extension. Checking happens in the scope @p@ that the parameters
-- extend the module's scope @n@ to; the discharged declaration has to come back
-- to @n@, because @n@ is where the module's exports live and where the next
-- module starts.
--
-- 'discharge' walks the telescope from the inside out and, at each parameter,
-- simply asks 'unsinkAST' whether the term can do without it:
--
-- * if it can, the parameter is dropped, and the term is now one scope smaller;
-- * if it cannot, the parameter is abstracted over, with @Π@ for the type and
--   @λ@ for the value.
--
-- So the set of parameters a declaration uses is not declared and believed, and
-- not computed by a separate analysis either: it is whatever restriction turns
-- out to reject. That also makes the set upward closed in the telescope for
-- free. Keeping @(x : A)@ puts @A@ into the discharged /type/, so the next step
-- out cannot drop @A@ even when the declaration's body never mentions it.
module Language.MLTT.Telescope where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil      (unsinkAST)
import           Data.List                    (intercalate, sort)
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve        (prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs     as Raw

-- | The parameters of a module: a name, a type, and a binder, in order.
--
-- The type of a parameter may mention the parameters before it, which is what
-- makes this a telescope rather than a list, and is why each entry records the
-- scope it sits in. That scope is what 'unsinkAST' needs in order to drop the
-- parameter again.
data Telescope a n l where
  TelescopeEmpty :: Telescope a n n
  TelescopeCons
    :: (Foil.Distinct n, Foil.DExt n i)
    => Raw.VarIdent           -- ^ How the parameter is spelled.
    -> Term' a n              -- ^ Its type, in the scope before it.
    -> Foil.Scope n           -- ^ That scope.
    -> Foil.NameBinder n i    -- ^ The binder that introduced it.
    -> Telescope a i l        -- ^ The parameters after it.
    -> Telescope a n l

-- | The parameters, outermost first.
telescopeNames :: Telescope a n l -> [Raw.VarIdent]
telescopeNames TelescopeEmpty                        = []
telescopeNames (TelescopeCons name _ _ _ rest) = name : telescopeNames rest

-- | A declaration after discharge: closed over the module's parameters.
data Discharged a n = Discharged
  { dischargedType  :: Term' a n
    -- ^ The type, wrapped in a @Π@ for each parameter used.
  , dischargedValue :: Term' a n
    -- ^ The value, wrapped in a @λ@ for each parameter used.
  , dischargedOver  :: [Raw.VarIdent]
    -- ^ Which parameters those were, outermost first.
  }

-- | Discharge a checked declaration over the parameters it uses.
--
-- The type and the value are discharged together, over the same parameters,
-- since @f : T@ and @f := v@ have to stay a matching pair: if only the value
-- mentions a parameter, the type still gains a (non-dependent) @Π@ for it.
discharge
  :: a                  -- ^ The position to put on the abstractions introduced.
  -> Telescope a n l
  -> Term' a l          -- ^ The declaration's type, checked with parameters in scope.
  -> Term' a l          -- ^ Its value, likewise.
  -> Discharged a n
discharge _loc TelescopeEmpty ty value = Discharged ty value []
discharge loc (TelescopeCons name paramTy scope binder rest) ty value =
  case (unsinkAST scope inner, unsinkAST scope innerValue) of
    -- Neither side mentions the parameter, so the declaration does not use it.
    (Just ty', Just value') -> Discharged ty' value' over
    -- One of them does. Abstract over it, and note it as used.
    _ -> Discharged
      { dischargedType  = Pi loc paramTy (PatternVar loc binder) inner
      , dischargedValue = Lam loc (PatternVar loc binder) innerValue
      , dischargedOver  = name : over
      }
  where
    Discharged inner innerValue over = discharge loc rest ty value

-- | Check a declared @over@ clause against the parameters actually used.
--
-- The clause is optional, and it never changes what is discharged: the computed
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
