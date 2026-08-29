{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | The labelled telescope: a chain of binders, each carrying a label and a
-- payload in the scope before it.
--
-- This is the pattern behind a module's parameter block, a record signature,
-- or an algebraic theory: @(A : 𝕌) (m : A → A → A)@ is a two-step
-- telescope whose second payload mentions the first binder. Because a
-- telescope is a pattern ('CoSinkable', 'UnifiablePattern'), scope extension,
-- the names of a block, and α-equivalence of blocks come from the pattern
-- machinery, with the payloads compared through 'AlphaEquiv'.
--
-- What this module does not fix is what a payload /is/. The payload type is a
-- parameter, and the operations that need to look inside one, such as the
-- support a dependency closure needs, take the looking function as an
-- argument. A client instantiates the labels and payloads to its own types.
-- To close a declaration over the fields it uses, apply 'closeOverTelescope'
-- and then 'withThinnedNameBinderList'.
module Control.Monad.Foil.Telescope where

import           Control.Monad.Foil.Internal
import           Control.Monad.Foil.Relative (RelMonad, liftRM)

-- | A labelled telescope: a chain of binders, each carrying a label and a
-- payload in the scope before it.
--
-- The payload of a step lives in the scope the steps before it extend to, which
-- is what makes this a telescope rather than a list. For a module's parameters
-- the label is how the parameter is spelled and the payload is its type, so
-- that @(A : 𝕌) (m : A → A → A)@ is a two-step telescope whose second payload
-- mentions the first binder.
--
-- See 'NameBinderList', which this follows almost line for line.
data Telescope label e n l where
  TelescopeEmpty :: Telescope label e n n
  TelescopeCons
    :: label                        -- ^ How the step is labelled.
    -> e n                          -- ^ Its payload, in the scope before it.
    -> NameBinder n i          -- ^ The binder it introduces.
    -> Telescope label e i l        -- ^ The steps after it.
    -> Telescope label e n l

-- | A telescope is a pattern, so the foil's own machinery walks it.
--
-- 'coSinkabilityProof' typechecks only because a payload is sunk by the
-- renaming of the scope /before/ its binder, rather than by the extended one.
--
-- 'withPattern' has to be written out rather than derived. The generic
-- implementation refuses a pattern with a field indexed by a scope, since it
-- would leave a payload that names a refreshed binder pointing at the name
-- that binder used to have. This instance follows the recipe in
-- 'transportPayload': a 'PatternTransport' threaded through the traversal,
-- with each payload moved by the transport accumulated /before/ its own
-- binder, that being the scope the payload lives in.
instance Sinkable e => CoSinkable (Telescope label e) where
  coSinkabilityProof rename TelescopeEmpty cont = cont rename TelescopeEmpty
  coSinkabilityProof rename (TelescopeCons label payload binder rest) cont =
    coSinkabilityProof rename binder $ \rename' binder' ->
      coSinkabilityProof rename' rest $ \rename'' rest' ->
        cont rename''
          (TelescopeCons label (sinkabilityProof rename payload) binder' rest')

  withPattern
    :: forall f o n l r. Distinct o
    => (forall x y z r'. Distinct z
          => Scope z
          -> NameBinder x y
          -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r')
          -> r')
    -> (forall x z z'. DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (DExt z z', DExt z' z'')
          => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Scope o
    -> Telescope label e n l
    -> (forall o'. DExt o o' => f n l o o' -> Telescope label e o o' -> Scope o' -> r)
    -> r
  withPattern withBinder unit comp = go verbatimTransport
    where
      go :: forall n' l' o' r'. Distinct o'
         => PatternTransport n' o'
         -> Scope o'
         -> Telescope label e n' l'
         -> (forall o''. DExt o' o''
               => f n' l' o' o'' -> Telescope label e o' o'' -> Scope o'' -> r')
         -> r'
      go _transport scope TelescopeEmpty cont = cont unit TelescopeEmpty scope
      go transport scope (TelescopeCons label payload binder rest) cont =
        withBinder scope binder $ \fbinder binder' ->
          go (transportUnderBinder transport binder binder')
             (extendScope binder' scope)
             rest $ \frest rest' scope'' ->
            cont (comp fbinder frest)
              (TelescopeCons label (transportPayload transport payload) binder' rest')
              scope''

-- | Two telescopes unify when their binders line up and their payloads agree.
--
-- Labels are ignored, which is what α-equivalence should do with a label: a
-- parameter's spelling is no more relevant than a bound variable's. Payloads
-- are not, since two telescopes agreeing on binders may well disagree on types.
--
-- 'unifyPatterns' is the binder-only approximation, which is all a caller
-- without a scope can be given. 'unifyPatternsIn' is the real answer, and
-- it is what the library's α-equivalence calls.
instance (Sinkable e, AlphaEquiv e, RelMonad Name e)
    => UnifiablePattern (Telescope label e) where
  unifyPatterns TelescopeEmpty TelescopeEmpty =
    SameNameBinders emptyNameBinders
  unifyPatterns (TelescopeCons _ _ x xs) (TelescopeCons _ _ y ys) =
    case (assertDistinct x, assertDistinct y) of
      (Distinct, Distinct) ->
        unifyNameBinders x y `andThenUnifyPatterns` (xs, ys)
  -- Telescopes of different lengths bind different numbers of names.
  unifyPatterns _ _ = NotUnifiable

  unifyPatternsIn scope tele1 tele2
    | payloadsAgree scope tele1 tele2 verdict = verdict
    | otherwise                               = NotUnifiable
    where
      verdict = unifyPatterns tele1 tele2

-- | The payloads of a telescope, each moved into its innermost scope.
--
-- Sinking is free, so putting them all in one scope costs nothing and lets a
-- renaming be applied to the whole block at once.
telescopePayloads
  :: (Sinkable e, Distinct l) => Telescope label e n l -> [e l]
telescopePayloads = map paramType . telescopeParams

-- | Do the payloads of two telescopes agree, under the way their binders were
-- unified?
--
-- The verdict speaks about binders only, so the renaming it prescribes has to
-- be applied before the payloads are compared, which is exactly what
-- 'Control.Monad.Free.alphaEquivScoped' does to the body of a scoped term.
-- Comparing them as they stand would report @(A : 𝕌) (x : A)@ and
-- @(B : 𝕌) (y : B)@ as different, since the second payloads name different
-- binders until the first ones have been identified.
payloadsAgree
  :: forall label e n l r.
     (Sinkable e, AlphaEquiv e, RelMonad Name e, Distinct n)
  => Scope n
  -> Telescope label e n l
  -> Telescope label e n r
  -> UnifyNameBinders (Telescope label e) n l r
  -> Bool
payloadsAgree scope tele1 tele2 verdict =
  case (assertDistinct tele1, assertDistinct tele2) of
    (Distinct, Distinct) ->
      let payloads1 = telescopePayloads tele1
          payloads2 = telescopePayloads tele2
       in case verdict of
            NotUnifiable -> False
            -- The binders are the same, so the payloads already compare.
            SameNameBinders{} ->
              agree (extendScopePattern tele1 scope) payloads1 payloads2
            -- The left telescope's binders become the right's, so its payloads
            -- have to follow them before they can be compared.
            RenameLeftNameBinder _ renameL ->
              let scope' = extendScopePattern tele2 scope
               in agree scope' (map (rename scope' renameL) payloads1) payloads2
            RenameRightNameBinder _ renameR ->
              let scope' = extendScopePattern tele1 scope
               in agree scope' payloads1 (map (rename scope' renameR) payloads2)
            -- Neither side's binders survive, so both blocks move to the
            -- unified ones.
            RenameBothBinders binders renameL renameR ->
              case assertDistinct binders of
                Distinct ->
                  let scope' = extendScopePattern binders scope
                   in agree scope' (map (rename scope' renameL) payloads1)
                                   (map (rename scope' renameR) payloads2)
  where
    -- Lengths cannot disagree here: a verdict other than 'NotUnifiable'
    -- says the two telescopes bind the same number of names.
    agree :: forall m. Distinct m => Scope m -> [e m] -> [e m] -> Bool
    agree scope' xs ys = and (zipWith (alphaEquivIn scope') xs ys)

    rename
      :: forall i m. Distinct m
      => Scope m -> (NameBinder n i -> NameBinder n m) -> e i -> e m
    rename scope' f = liftRM scope' (fromNameBinderRenaming f)

-- | One step of a telescope, with everything about it moved into the innermost
-- scope.
--
-- Sinking is free, so this is the convenient form for anything that has to
-- compare parameters with the names of a term checked under all of them.
data Param label e l = Param
  { paramLabel :: label
  , paramName  :: Name l
  , paramType  :: e l
  }

-- | The steps of a telescope, outermost first.
telescopeParams
  :: (Sinkable e, Distinct l)
  => Telescope label e n l -> [Param label e l]
telescopeParams TelescopeEmpty = []
telescopeParams (TelescopeCons label ty binder rest) =
  case (assertExt binder, assertExt rest) of
    (Ext, Ext) ->
      Param label (sink (nameOf binder)) (sink ty)
        : telescopeParams rest

-- | The chain of binders a telescope forms.
--
-- This is 'nameBinderListOf' at a telescope, written out. The general one
-- goes through 'withPattern' and so rebuilds the telescope only to throw it
-- away, which is worth avoiding on the checking path.
telescopeBinders :: Telescope label e n l -> NameBinderList n l
telescopeBinders TelescopeEmpty = NameBinderListEmpty
telescopeBinders (TelescopeCons _ _ binder rest) =
  NameBinderListCons binder (telescopeBinders rest)

-- | Close a set of parameters under the parameters their payloads need.
--
-- Keeping a parameter puts its payload into the result, so whatever that
-- payload mentions has to be kept too. A payload mentions only the parameters
-- before it, so working from the inside out settles it in one pass.
--
-- The support of a payload is the caller's to supply, since the library does
-- not know what a payload is. For terms of the free foil it is
-- 'Control.Monad.Free.Foil.supportOf'.
closeOverTelescope
  :: Distinct l
  => (e l -> NameSet l)  -- ^ The support of a payload.
  -> [Param label e l] -> NameSet l -> NameSet l
closeOverTelescope supportOfPayload params wanted = foldr close wanted params
  where
    close p keep
      | nameSetMember (paramName p) keep = keep <> supportOfPayload (paramType p)
      | otherwise                        = keep

