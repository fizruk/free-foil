{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | The labelled telescope, module parameters as an instance of it, and closing
-- a declaration over the parameters it uses.
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
-- The parameters may come from an @include@ rather than be written out; that is
-- resolved before a module is checked (see 'Language.MLTT.Impl.resolveUnits'),
-- so nothing here can tell the difference.
--
-- == Where the scope restriction is
--
-- This is the place the demo needs free-foil's scope /restriction/ rather than
-- its extension. Checking happens in the scope @p@ that the parameters extend
-- the module's scope @n@ to; the result has to come back to @n@, because @n@ is
-- where the module's exports live and where the next module starts.
--
-- It is done in three steps, and the point of the arrangement is that the term
-- is walked a fixed number of times rather than once per parameter:
--
-- 1. 'supportOf' the type and the value, once each.
-- 2. 'closeOverTelescope' closes that set under the parameter types. Keeping
--    @(x : A)@ puts @A@ into the result, so @A@ has to be kept as well. One
--    pass from the inside out is enough, since a parameter's type mentions only
--    the parameters before it.
-- 3. 'Foil.withThinnedNameBinderList' cuts the chain of binders down to that
--    set in one step, and 'discharge' rebuilds the abstractions along the
--    thinned chain, restricting each parameter type and the body into it.
--
-- The alternative, asking 'unsinkAST' at every parameter whether the term can
-- do without it, is shorter to write and walks the whole term once per
-- parameter.
module Language.MLTT.Telescope where

import qualified Control.Monad.Foil           as Foil
import           Control.Monad.Free.Foil      (supportOf, unsinkAST)
import           Data.List                    (intercalate, sort)
import           Unsafe.Coerce                (unsafeCoerce)

import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve        (prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs     as Raw

-- | A labelled telescope: a chain of binders, each carrying a label and a
-- payload in the scope before it.
--
-- The payload of a step lives in the scope the steps before it extend to, which
-- is what makes this a telescope rather than a list. For a module's parameters
-- the label is how the parameter is spelled and the payload is its type, so
-- that @(A : 𝕌) (m : A → A → A)@ is a two-step telescope whose second payload
-- mentions the first binder.
--
-- Nothing here is specific to MLTT, and the intention is to lift the type and
-- its instances into free-foil once they have been proven in the demo. See
-- 'Foil.NameBinderList', which this follows almost line for line.
data Telescope label e n l where
  TelescopeEmpty :: Telescope label e n n
  TelescopeCons
    :: label                        -- ^ How the step is labelled.
    -> e n                          -- ^ Its payload, in the scope before it.
    -> Foil.NameBinder n i          -- ^ The binder it introduces.
    -> Telescope label e i l        -- ^ The steps after it.
    -> Telescope label e n l

-- | A module's parameters: the labels are spellings, the payloads are types.
type ParamTelescope a = Telescope Raw.VarIdent (Term' a)

-- | How a payload is moved from a telescope's own scope into the ambient one.
--
-- 'Foil.withPattern' relates the two scopes only through the binders it hands
-- back, so this is accumulated as the telescope is walked: a step whose binder
-- came back unchanged leaves raw names alone, and only a step that renamed its
-- binder makes the transport a real renaming. Since 'Foil.extendScopePattern',
-- 'Foil.namesOfPattern' and 'Foil.nameBinderListOf' never rename, the payloads
-- are not walked on any of those paths.
data Transport n o
  = Verbatim
    -- ^ No binder was renamed, so the payload can be taken over as it is.
  | Renamed (Foil.Name n -> Foil.Name o)
    -- ^ Some binder was renamed, so the payload has to be traversed.

-- | Move a payload along a 'Transport'.
transportPayload :: Foil.Sinkable e => Transport n o -> e n -> e o
transportPayload Verbatim         = unsafeCoerce
transportPayload (Renamed rename) = Foil.sinkabilityProof rename

-- | Move a single name along a 'Transport'.
transportName :: Transport n o -> Foil.Name n -> Foil.Name o
transportName Verbatim         = unsafeCoerce
transportName (Renamed rename) = rename

-- | Extend a transport by one step of the telescope.
--
-- The names of the inner scope are the binder's own name, which goes to the
-- name the refreshed binder introduces, and the names of the outer scope, which
-- the transport so far already answers for.
extendTransport
  :: Transport n o
  -> Foil.NameBinder n i    -- ^ The binder as the telescope has it.
  -> Foil.NameBinder o o'   -- ^ The binder 'Foil.withPattern' handed back.
  -> Transport i o'
extendTransport transport binder binder'
  | Verbatim <- transport, unchanged = Verbatim
  | otherwise = Renamed $ \name ->
      if Foil.nameId name == Foil.nameId (Foil.nameOf binder)
        then Foil.nameOf binder'
        else unsafeCoerce (transportName transport (unsafeCoerce name))
  where
    unchanged =
      Foil.nameId (Foil.nameOf binder) == Foil.nameId (Foil.nameOf binder')

-- | A telescope is a pattern, so the foil's own machinery walks it.
--
-- 'Foil.coSinkabilityProof' is the interesting half. It is proof code (every
-- call site goes through 'Foil.extendRenaming', which is a coercion), but it
-- has to typecheck, and it only does because a payload is sunk by the renaming
-- of the scope /before/ its binder rather than by the extended one.
instance Foil.Sinkable e => Foil.CoSinkable (Telescope label e) where
  coSinkabilityProof rename TelescopeEmpty cont = cont rename TelescopeEmpty
  coSinkabilityProof rename (TelescopeCons label payload binder rest) cont =
    Foil.coSinkabilityProof rename binder $ \rename' binder' ->
      Foil.coSinkabilityProof rename' rest $ \rename'' rest' ->
        cont rename''
          (TelescopeCons label (Foil.sinkabilityProof rename payload) binder' rest')

  withPattern
    :: forall f o n l r. Foil.Distinct o
    => (forall x y z r'. Foil.Distinct z
          => Foil.Scope z
          -> Foil.NameBinder x y
          -> (forall z'. Foil.DExt z z' => f x y z z' -> Foil.NameBinder z z' -> r')
          -> r')
    -> (forall x z z'. Foil.DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (Foil.DExt z z', Foil.DExt z' z'')
          => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Foil.Scope o
    -> Telescope label e n l
    -> (forall o'. Foil.DExt o o' => f n l o o' -> Telescope label e o o' -> r)
    -> r
  withPattern withBinder unit comp = go Verbatim
    where
      go :: forall n' l' o' r'. Foil.Distinct o'
         => Transport n' o'
         -> Foil.Scope o'
         -> Telescope label e n' l'
         -> (forall o''. Foil.DExt o' o''
               => f n' l' o' o'' -> Telescope label e o' o'' -> r')
         -> r'
      go _transport _scope TelescopeEmpty cont = cont unit TelescopeEmpty
      go transport scope (TelescopeCons label payload binder rest) cont =
        withBinder scope binder $ \fbinder binder' ->
          go (extendTransport transport binder binder')
             (Foil.extendScope binder' scope)
             rest $ \frest rest' ->
            cont (comp fbinder frest)
              (TelescopeCons label (transportPayload transport payload) binder' rest')

-- | Telescopes unify exactly when their binders do, as for a
-- 'Foil.NameBinderList'.
--
-- Labels and payloads are ignored, which is the library's documented default
-- for non-binding fields, and is what α-equivalence should do with a label: a
-- parameter's spelling is no more relevant than a bound variable's. Payloads
-- are a different matter, since two telescopes agreeing on binders may well
-- disagree on types. Unfortunately 'Foil.unifyPatterns' has only
-- 'Foil.Distinct' to work with, and comparing terms up to α needs the scope, so
-- the caller has to compare the payloads itself.
instance Foil.Sinkable e => Foil.UnifiablePattern (Telescope label e) where
  unifyPatterns TelescopeEmpty TelescopeEmpty =
    Foil.SameNameBinders Foil.emptyNameBinders
  unifyPatterns (TelescopeCons _ _ x xs) (TelescopeCons _ _ y ys) =
    case (Foil.assertDistinct x, Foil.assertDistinct y) of
      (Foil.Distinct, Foil.Distinct) ->
        Foil.unifyNameBinders x y `Foil.andThenUnifyPatterns` (xs, ys)
  -- Telescopes of different lengths bind different numbers of names.
  unifyPatterns _ _ = Foil.NotUnifiable

-- | One step of a telescope, with everything about it moved into the innermost
-- scope.
--
-- Sinking is free, so this is the convenient form for anything that has to
-- compare parameters with the names of a term checked under all of them.
data Param label e l = Param
  { paramLabel :: label
  , paramName  :: Foil.Name l
  , paramType  :: e l
  }

-- | The steps of a telescope, outermost first.
telescopeParams
  :: (Foil.Sinkable e, Foil.Distinct l)
  => Telescope label e n l -> [Param label e l]
telescopeParams TelescopeEmpty = []
telescopeParams (TelescopeCons label ty binder rest) =
  case (Foil.assertExt binder, Foil.assertExt rest) of
    (Foil.Ext, Foil.Ext) ->
      Param label (Foil.sink (Foil.nameOf binder)) (Foil.sink ty)
        : telescopeParams rest

-- | The chain of binders a telescope forms.
--
-- This is 'Foil.nameBinderListOf' at a telescope, written out: the general one
-- goes through 'Foil.withPattern' and so rebuilds the telescope only to throw
-- it away, and this is on the checking path.
telescopeBinders :: Telescope label e n l -> Foil.NameBinderList n l
telescopeBinders TelescopeEmpty = Foil.NameBinderListEmpty
telescopeBinders (TelescopeCons _ _ binder rest) =
  Foil.NameBinderListCons binder (telescopeBinders rest)

-- | Close a set of parameters under the parameters their types need.
--
-- Keeping a parameter puts its type into the result, so whatever that type
-- mentions has to be kept too. A parameter's type mentions only the parameters
-- before it, so working from the inside out settles it in one pass.
closeOverTelescope
  :: Foil.Distinct l
  => [Param label (Term' a) l] -> Foil.NameSet l -> Foil.NameSet l
closeOverTelescope params wanted = foldr close wanted params
  where
    close p keep
      | Foil.nameSetMember (paramName p) keep = keep <> supportOf (paramType p)
      | otherwise                             = keep

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
    needed = closeOverTelescope params (supportOf ty <> supportOf value)

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
