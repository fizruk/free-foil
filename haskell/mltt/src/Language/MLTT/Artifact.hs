{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Serialisation of checked modules.
--
-- A raw name of a /constant/ is a registry artefact. The artifact therefore
-- records the constants' qualified spellings, and loading judges them once,
-- at the artifact level ('constantRelocation'). In the usual case every
-- constant already means here what it meant at check time, and the terms
-- are used exactly as decoded; no term is walked at all. Where the registry
-- moved, one total relocation pass touches the references. A loaded module
-- is an ordinary 'CheckedModule': it links, and further modules check
-- against it, exactly as if it had just been checked.
--
-- What makes the cache valid is recorded alongside the terms:
--
-- * the name ranges at check time: the actual names of the module's own
--   constants, and of its locals. These are ranges rather than a stripe
--   index, so the artifact does not depend on the loading build's stripe
--   policy. A run whose registry agrees reconstructs the very same raw
--   names, and one whose registry moved the reservation still loads, with
--   the names landing where the new range says. Moreover, the no-overlap
--   assumption the verbatim terms rest on is checked from the recorded
--   ranges, never from the terms;
-- * the content hash of each import at check time, so a changed dependency
--   is detected and the artifact rejected rather than linked stale.
--
-- __Loading trusts the artifact's terms__: nothing is re-checked. This
-- covers the typing, and equally the locals and their scoping. What is
-- judged is the constants' boundary, and it is judged from the spelling
-- table alone, not from the terms. Integrity comes from the hash chain,
-- and the hash is 'contentHash', a plain FNV-1a over the stored content:
-- collision resistance enough for a build cache, not for an adversary.
--
-- Terms are stored verbatim ('encodeTerm'). The name layout's sign
-- invariant is what makes the raw ids meaningful: a negative name is an
-- interned constant, resolved by spelling on load, and a non-negative one
-- is a local, canonical by elaboration. Nothing is parsed on load, no
-- spelling ever needs escaping, and the bytes do not depend on what else
-- was in scope at check time. Thus the same module produces an identical
-- artifact, and an identical hash, whatever world it is checked in.
module Language.MLTT.Artifact (
  ModuleArtifact (..),
  ArtifactDecl (..),
  ContentHash (..),
  StoredTerm (..),
  ArtifactError,
  makeArtifact,
  loadArtifact,
  loadArtifactAfter,
  encodeArtifact,
  decodeArtifact,
  contentHash,
) where

import           Control.Monad             (unless)
import qualified Control.Monad.Foil        as Foil
import qualified Control.Monad.Foil.Internal as Foil.Internal
import           Control.Monad.Free.Foil   (AST (..), ScopedAST (..),
                                            supportOf)
import           Control.Monad.Free.Foil.Binary ()
import qualified Control.Monad.Foil.Blocks as Blocks
import           Data.Binary               (Binary (..))
import           Data.Binary.Get           (runGetOrFail)
import qualified Data.Binary.Get           as Get
import           Data.Binary.Put           (runPut)
import qualified Data.Binary.Put           as Put
import           Data.Bifoldable           (bifoldMap)
import           Data.Bifunctor            (bimap)
import           Unsafe.Coerce             (unsafeCoerce)
import           Data.Bits                 (xor, (.&.))
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.Char8 as BSL8
import           Data.List                 (foldl')
import qualified Data.IntMap               as IntMap
import           Data.Map                  (Map)
import           GHC.Generics              (Generic)
import qualified Data.Map                  as Map

import           Language.MLTT.Eval        (Def (..))
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve     (Visibility (..), prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs  as Raw
import           Language.MLTT.Typecheck   (Ctx (..), extend)

-- * The artifact

-- | A checked module, as written to disk.
data ModuleArtifact = ModuleArtifact
  { artifactModule  :: Raw.VarIdent  -- ^ The module's qualified name.
  , artifactConstants :: Foil.NameRange
      -- ^ The actual names of the module's own constants: the used prefix
      -- of its reservation, recorded as the range itself. Thus the
      -- artifact depends neither on the loading build's stripe policy nor
      -- on the writer's reservation size, and it loads anywhere its names
      -- actually fit. Note that the range is exactly its declarations,
      -- which decoding checks.
  , artifactLocals  :: Foil.NameRange
      -- ^ The actual range of the stored terms' locals: the names their
      -- binders bind, not the writer's whole local region. It is recorded
      -- so that the no-overlap assumption the verbatim terms rest on is a
      -- checkable fact of the artifact, not a convention shared with the
      -- writer. It is the actual range so that the check is tight.
  , artifactSource  :: ContentHash   -- ^ Of the module's printed source:
                                     -- what an incremental rebuild compares.
  , artifactImports :: [(Raw.VarIdent, ContentHash)]
      -- ^ Each import, with its content hash at check time.
  , artifactHash    :: ContentHash   -- ^ Over the spellings and declarations below.
  , artifactSpellings :: Map Foil.RawName Raw.VarIdent
      -- ^ The fully qualified spelling of every constant the stored terms
      -- reference. There is one table for the whole artifact, since the
      -- module's declarations largely reference the same imports.
  , artifactDecls   :: [ArtifactDecl] -- ^ In declaration (= allocation) order.
  }
  deriving (Eq, Show, Generic)

-- | Field order from the 'Generic' shape; 'encodeArtifact' adds the
-- envelope.
instance Binary ModuleArtifact

-- | One declaration: everything the environment needs to hold for it.
data ArtifactDecl = ArtifactDecl
  { adSpelling   :: Raw.VarIdent  -- ^ Fully qualified.
  , adVisibility :: Visibility
  , adType       :: StoredTerm
  , adValue      :: StoredTerm
  }
  deriving (Eq, Show, Generic)

instance Binary ArtifactDecl

-- | A term as stored: the canonical bytes of the pair of its spelling table
-- and the term itself ('encodeTerm'). Equality of stored terms is byte
-- equality, which is what the canonical-artifact property tests.
newtype StoredTerm = StoredTerm { storedBytes :: BSL.ByteString }
  deriving (Eq, Show, Generic)

instance Binary StoredTerm

-- | Encode a checked term, verbatim, through the @free-foil-binary@
-- instances.
--
-- The name layout's sign invariant is what makes verbatim enough. A name
-- below zero is an interned constant, whose spelling the artifact's table
-- records; note that a term's free variables are exactly its constants,
-- since a stored declaration is discharged. A non-negative name is a
-- local, and needs no table: it is canonical already, since elaboration
-- allocates locals in a region of their own.
encodeTerm :: Term n -> BSL.ByteString
encodeTerm t = runPut (put t)

-- | Decode a stored term's bytes: the instances alone, no meaning yet.
-- Meaning is given per artifact, not per term — see 'constantRelocation'.
decodeStored :: StoredTerm -> Either ArtifactError (Term n)
decodeStored (StoredTerm bytes) =
  case runGetOrFail get bytes of
    Left (_, _, err) -> Left ("malformed stored term: " <> err)
    Right (rest, _, term)
      | not (BSL.null rest) -> Left "malformed stored term: trailing bytes"
      | otherwise -> Right term

-- | What an artifact's constants need in the loading world, judged once,
-- from the spelling table alone. 'Nothing' says every constant already has
-- the id its spelling means here; this is the fast path, on which no term
-- is walked at all. Otherwise the result is the renaming to apply. Its
-- domain is a scope of the artifact's world, which no longer exists, so
-- its index is the caller's phantom.
--
-- The module's own constants (table entries inside the recorded range) do
-- not consult the world: they are being loaded right now, in the same
-- order they were allocated, so their relocation is the affine shift
-- between the recorded range and the one this run assigned. Their new
-- names are thereby minted ahead of their allocation, which loading's
-- trust covers. An imported constant resolves by its spelling; one this
-- world does not know is reported.
constantRelocation
  :: Foil.NameRange                 -- ^ The recorded range of its own constants.
  -> Foil.NameRange                 -- ^ The range this run assigned.
  -> Foil.NameRange                 -- ^ The artifact's recorded locals region.
  -> Map Foil.RawName Raw.VarIdent  -- ^ The artifact's spelling table.
  -> Map Raw.VarIdent (Foil.Name n') -- ^ What each spelling means here.
  -> Either ArtifactError (Maybe (Foil.NameMap old (Foil.Name n')))
constantRelocation old@(Foil.NameRange oldLo _) (Foil.NameRange newLo _) locals table globals = do
  entries <- Map.foldrWithKey step (Right []) table
  pure $
    if any (\(i, name) -> Foil.nameId name /= i) entries
      then Just (Foil.Internal.NameMap (IntMap.fromList entries))
      else Nothing
  where
    shift = newLo - oldLo
    -- Every relocation target must stay out of the locals region: the
    -- verbatim locals rest on the two never meeting, and this is where the
    -- assumption is checked — per constant, at the artifact level, never
    -- per term.
    step i spelling acc = do
      rest <- acc
      name <-
        if withinRange old i
          then Right (Foil.Internal.UnsafeName (i + shift))
          else case Map.lookup spelling globals of
            Nothing   -> Left ("not in scope: " <> prettyVarIdent spelling)
            Just name -> Right name
      if withinRange locals (Foil.nameId name)
        then Left ("constant " <> prettyVarIdent spelling
                     <> " would land in the locals region")
        else pure ((i, name) : rest)

-- | Whether a raw name lies in a range.
withinRange :: Foil.NameRange -> Foil.RawName -> Bool
withinRange (Foil.NameRange lo hi) i = lo <= i && i <= hi

-- | Rename every constant reference through the map, moving the term from
-- the artifact's world into the loading one. This is the restriction to
-- constants of a general renaming @'Foil.Name' n -> 'Foil.Name' n'@.
-- 'Foil.sinkabilityProof' embodies the general renaming, but its efficient
-- implementations degenerate the renaming to a coercion under binders,
-- which is sound only for inclusions; this walk carries an arbitrary map
-- through.
--
-- The invariant that lets the walk ignore the binders is the sign layout.
-- Constants live below zero, and a binder binds locals, at or above zero.
-- Thus no binder can shadow a name in the map's domain, and no local can
-- be in it, so the map never needs extending under a binder, and locals
-- and patterns cross by coercion. A constant outside the map (bytes
-- referencing something the spelling table does not cover) is re-minted
-- unchanged, trusted like everything else about the term. Note that a map
-- that is the identity on raw ids would make the whole walk a coercion,
-- which is why the caller skips it entirely then.
relocateConstants :: Foil.NameMap n (Foil.Name n') -> Term n -> Term n'
relocateConstants (Foil.Internal.NameMap moved) = walk
  where
    walk :: forall o o'. Term o -> Term o'
    walk = \case
      Var x -> case IntMap.lookup (Foil.nameId x) moved of
        Just new -> Var (Foil.Internal.UnsafeName (Foil.nameId new))
        Nothing  -> Var (Foil.Internal.UnsafeName (Foil.nameId x))
      Node sig -> Node (bimap walkScoped walk sig)

    walkScoped :: forall o o'. ScopedTerm o -> ScopedTerm o'
    walkScoped (ScopedAST pat body) = ScopedAST (unsafeCoerce pat) (walk body)

-- | The 64-bit FNV-1a of some rendered content; see 'contentHash'.
newtype ContentHash = ContentHash Integer
  deriving (Eq, Show, Generic)

instance Binary ContentHash

-- | What reading or loading an artifact can report: malformed wire bytes, a
-- stale import hash, or a stored term that no longer resolves.
type ArtifactError = String

-- | FNV-1a over a string, 64 bits. A build-cache checksum, not a defence.
contentHash :: String -> ContentHash
contentHash = ContentHash . foldl' step fnvBasis . map fromEnum
  where
    step h c = fnvStep h (fromIntegral c)

-- | The same FNV-1a, over bytes: what the artifact hash uses, so that the
-- hash covers exactly the stored representation.
contentHashBytes :: BSL.ByteString -> ContentHash
contentHashBytes = ContentHash . BSL.foldl' step fnvBasis
  where
    step h w = fnvStep h (fromIntegral w)

fnvBasis :: Integer
fnvBasis = 0xcbf29ce484222325

fnvStep :: Integer -> Integer -> Integer
fnvStep h x = ((h `xor` x) * 0x100000001b3) .&. 0xffffffffffffffff

-- * The envelope

-- | The first bytes of an artifact file: decoding /is/ the check, so a file
-- that is not an artifact is reported rather than misread.
data WireMagic = WireMagic

instance Binary WireMagic where
  put WireMagic = Put.putLazyByteString magicBytes
  get = do
    bytes <- Get.getLazyByteString (BSL.length magicBytes)
    unless (bytes == magicBytes) (fail "not an MLTT artifact")
    pure WireMagic

magicBytes :: BSL.ByteString
magicBytes = BSL8.pack "MLTTA"

-- | Bumped when the format changes shape; decoding any other version fails,
-- and the cache treats the artifact as absent, so it is rebuilt.
data WireVersion = WireVersion

instance Binary WireVersion where
  put WireVersion = put wireVersion
  get = do
    version <- get
    unless (version == wireVersion) $
      fail ("format version " <> show version
              <> ", but this build reads version " <> show wireVersion)
    pure WireVersion

wireVersion :: Word
wireVersion = 1

-- | Encode an artifact for writing: the envelope, then the derived
-- instances. 'decodeArtifact' is its inverse.
encodeArtifact :: ModuleArtifact -> BSL.ByteString
encodeArtifact a = runPut (put (WireMagic, WireVersion, a))

-- | Decode an artifact; reports rather than crashes on anything that is not
-- a current-version artifact. Beyond the envelope, the one shape check the
-- instances cannot express: a spelling-table entry for a non-negative name
-- would spell a non-constant.
decodeArtifact :: BSL.ByteString -> Either ArtifactError ModuleArtifact
decodeArtifact input = case runGetOrFail get input of
  Left (_, _, err) -> Left ("malformed artifact: " <> err)
  Right (rest, _, (WireMagic, WireVersion, a))
    | not (BSL.null rest) -> Left "malformed artifact: trailing bytes"
    | overlapping (artifactConstants a) (artifactLocals a) ->
        Left "malformed artifact: the constants and locals regions overlap"
    | any (withinRange (artifactLocals a)) (Map.keys (artifactSpellings a)) ->
        Left "malformed artifact: a spelling for a local"
    | rangeSize (artifactConstants a) /= length (artifactDecls a) ->
        Left "malformed artifact: the constants range does not match the declarations"
    | otherwise -> Right a
  where
    overlapping (Foil.NameRange lo1 hi1) (Foil.NameRange lo2 hi2) =
      lo1 <= hi1 && lo2 <= hi2 && lo1 <= hi2 && lo2 <= hi1
    rangeSize (Foil.NameRange lo hi) = max 0 (hi - lo + 1)

-- * Writing

-- | Serialise a checked module.
--
-- The declarations are exactly the names the module allocated in its stripe,
-- in ascending order, which is declaration order; their spellings come from
-- 'envDisplay' and are fully qualified, so the artifact does not depend on
-- what was visible under which shorter spelling at check time.
makeArtifact
  :: Raw.VarIdent               -- ^ The module's name.
  -> Foil.NameRange             -- ^ Its reservation, from the registry.
  -> ContentHash                -- ^ Of the module's printed source.
  -> [(Raw.VarIdent, ContentHash)] -- ^ Its imports, with their content hashes.
  -> CheckedModule c
  -> ModuleArtifact
makeArtifact name reservation source imports cm = withCheckedModule cm $ \_ env _ ->
  let Foil.NameRange lo hi = reservation
      constants = case map Foil.nameId own of
        [] -> Foil.NameRange lo (lo - 1)   -- empty, by the lo > hi convention
        ids -> Foil.NameRange (minimum ids) (maximum ids)
      locals = case concat localIds of
        [] -> Foil.NameRange 0 (-1)        -- empty likewise
        ids -> Foil.NameRange (minimum ids) (maximum ids)
      ctx = envCtx env
      own =
        [ x
        | x <- Foil.nameSetToList (Foil.scopeToNameSet (ctxScope ctx))
        , lo <= Foil.nameId x, Foil.nameId x <= hi
        ]
      (decls, supports, localIds) = unzip3 (map declOf own)
      -- The module's support: every constant its stored terms reference,
      -- and only those. Only those, because the spelling table is hashed:
      -- an unused import must not change the artifact, or content-defined
      -- early cutoff dies — and a table of everything in scope would also
      -- differ between build schedules, breaking canonicity.
      spellings = Map.fromList
        [ (Foil.nameId x, Foil.lookupName x (envDisplay env))
        | x <- Foil.nameSetToList (mconcat supports)
        ]
      declOf x =
        let ty = Foil.lookupName x (ctxTypes ctx)
            value = case getDef (Foil.lookupName x (ctxDefs ctx)) of
              Just v  -> v
              Nothing -> error "impossible: a top-level name with no definition"
            spelling = Foil.lookupName x (envDisplay env)
         in ( ArtifactDecl
                { adSpelling   = spelling
                , adVisibility =
                    if Map.member spelling (envExports env) then Public else Private
                , adType       = StoredTerm (encodeTerm ty)
                , adValue      = StoredTerm (encodeTerm value)
                }
            , supportOf ty <> supportOf value
            , localsOf ty <> localsOf value )
   in ModuleArtifact
        { artifactModule  = name
        , artifactConstants = constants
        , artifactLocals  = locals
        , artifactSource  = source
        , artifactImports = imports
        , artifactHash    =
            contentHashBytes (runPut (put spellings <> put decls))
        , artifactSpellings = spellings
        , artifactDecls   = decls
        }

-- | The names a term's binders bind: what 'artifactLocals' ranges over.
-- Note that 'supportOf' cannot see them: they are bound, not free.
localsOf :: Term n -> [Foil.RawName]
localsOf = \case
  Var _    -> []
  Node sig -> bifoldMap scopedLocals localsOf sig
  where
    scopedLocals :: forall m. ScopedTerm m -> [Foil.RawName]
    scopedLocals (ScopedAST pat body) = patternIds pat <> localsOf body

    patternIds :: forall m l. Pattern' Raw.BNFC'Position m l -> [Foil.RawName]
    patternIds = \case
      PatternWildcard _ -> []
      PatternVar _ b    -> [Foil.nameId (Foil.nameOf b)]
      PatternPair _ a b -> patternIds a <> patternIds b

-- * Loading

-- | Load a checked module from its artifact, into an environment holding
-- what its imports export: the same starting point 'checkModule' has.
--
-- The load fails if an import's recorded content hash disagrees with the one
-- supplied, which is how a stale artifact is detected. It does not compare
-- the artifact's stripe with the range supplied: a registry that moved the
-- stripe is the relocation case, and the module simply loads at its new
-- names, consistently with everything else in this run.
loadArtifact
  :: forall c. Foil.Distinct c
  => Map Raw.VarIdent ContentHash
     -- ^ Content hashes of the modules loaded or checked so far.
  -> Foil.NameRange       -- ^ The module's stripe, from this run's registry.
  -> Env c                -- ^ Environment holding what its imports export.
  -> ModuleArtifact
  -> Either ArtifactError (CheckedModule c)
loadArtifact hashes range env artifact = do
  mapM_ checkImport (artifactImports artifact)
  relocation <- constantRelocation (artifactConstants artifact) range
                                   (artifactLocals artifact)
                                   (artifactSpellings artifact) (envDeclared env')
  go relocation (Blocks.beginBlock range) env' (artifactDecls artifact)
  where
    checkImport (m, h) = case Map.lookup m hashes of
      Just h' | h' == h -> Right ()
      Just _ -> Left (stale <> prettyVarIdent m <> " has changed since then")
      Nothing -> Left (stale <> prettyVarIdent m <> " is not among the modules loaded so far")
    stale = "stale artifact for " <> prettyVarIdent (artifactModule artifact) <> ": import "

    -- An import contributes the exporting module's public names, as in
    -- 'checkModule'; the artifact's own references are fully qualified, so
    -- no namespace-relative resolution is needed on top.
    env' = env
      { envDeclared = Map.unions
          [ Map.findWithDefault Map.empty m (envModules env)
          | (m, _) <- artifactImports artifact ]
      , envExports = Map.empty
      , envClosedOver = Map.empty
      }

    go :: forall old n. Foil.DExt c n
       => Maybe (Foil.NameMap old (Foil.Name c))
       -> Blocks.Block c n -> Env n -> [ArtifactDecl] -> Either ArtifactError (CheckedModule c)
    go _ block envN [] =
      Right (CheckedModule (Blocks.blockExt block)
                           (finishModule (artifactModule artifact) envN)
                           [])
    go relocation block envN (d : ds) = do
      ty    <- loadTerm relocation (adType d)
      value <- loadTerm relocation (adValue d)
      Blocks.withFreshInBlock block (ctxScope (envCtx envN)) $ \binder block' ->
        let ctx' = extend (envCtx envN) binder ty (Just value)
            envN' = extendEnv ctx' binder (adSpelling d) (adVisibility d) envN
         in go relocation block' envN' ds

    -- The stored term is the checked (hence desugared) one. On the fast
    -- path it is used exactly as decoded — the phantom index is simply
    -- taken to be the caller's. Where the registry moved, the term decodes
    -- at the map's own phantom, relocates into the base world, and sinks to
    -- the scope at hand.
    loadTerm :: forall old m. Foil.DExt c m
             => Maybe (Foil.NameMap old (Foil.Name c)) -> StoredTerm
             -> Either ArtifactError (Term m)
    loadTerm relocation stored = case relocation of
      Nothing -> context (decodeStored stored)
      Just moved -> do
        t <- context (decodeStored stored)
        pure (Foil.sink (relocateConstants moved t))
      where
        context :: Either ArtifactError a -> Either ArtifactError a
        context = either
          (\err -> Left ("artifact for " <> prettyVarIdent (artifactModule artifact)
                            <> ": " <> err))
          Right

-- | Load a module from its artifact into the environment of an already
-- loaded (or checked) unit, composing the evidence: the load-side mirror of
-- 'checkModuleAfter', so a chain of cached modules folds into one unit over
-- the chain's base and links like anything else.
loadArtifactAfter
  :: Map Raw.VarIdent ContentHash
     -- ^ Content hashes of the modules loaded or checked so far.
  -> Foil.NameRange       -- ^ The next module's stripe, from this run's registry.
  -> CheckedModule c      -- ^ The chain so far.
  -> ModuleArtifact
  -> Either ArtifactError (CheckedModule c)
loadArtifactAfter hashes range (CheckedModule ext env results) artifact = do
  cm <- loadArtifact hashes range env artifact
  case cm of
    CheckedModule ext' env' results' ->
      Right (CheckedModule (Blocks.composeExtWithin ext ext') env' (results <> results'))
