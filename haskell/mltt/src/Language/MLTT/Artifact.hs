{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Serialisation of checked modules, built from the parts in
-- "Control.Monad.Free.Foil.Artifact"; what remains here is the artifact
-- record, its envelope, and the driver logic.
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
import           Control.Monad.Free.Foil.Artifact hiding (ArtifactError)
import qualified Control.Monad.Free.Foil.Artifact as Stored
import           Control.Monad.Free.Foil.Binary ()
import qualified Control.Monad.Foil.Blocks as Blocks
import           Data.Binary               (Binary (..))
import           Data.Binary.Get           (runGetOrFail)
import qualified Data.Binary.Get           as Get
import           Data.Binary.Put           (runPut)
import qualified Data.Binary.Put           as Put
import           Data.Bits                 (xor, (.&.))
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.Char8 as BSL8
import           Data.List                 (foldl')
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
  , artifactLayout  :: StoredLayout
      -- ^ The actual names of the module's own constants and of its
      -- locals. Thus the artifact depends neither on the loading build's
      -- stripe policy nor on the writer's reservation size, and it loads
      -- anywhere its names actually fit; the no-overlap assumption the
      -- verbatim terms rest on is a checkable fact of the artifact, and
      -- the check is tight.
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

-- | The 64-bit FNV-1a of some rendered content; see 'contentHash'.
newtype ContentHash = ContentHash Integer
  deriving (Eq, Show, Generic)

instance Binary ContentHash

-- | What reading or loading an artifact can report: malformed wire bytes, a
-- stale import hash, or a stored term that no longer resolves.
type ArtifactError = String

-- | Render a library-side error with mltt's spellings.
renderArtifactError :: Stored.ArtifactError Raw.VarIdent -> String
renderArtifactError = prettyArtifactError prettyVarIdent

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
    | otherwise ->
        case checkStoredLayout (artifactLayout a)
                               (artifactSpellings a) (length (artifactDecls a)) of
          Left err -> Left ("malformed artifact: " <> renderArtifactError err)
          Right () -> Right a

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
      emptyAt base = Foil.NameRange base (base - 1)
      layout = StoredLayout
        { storedConstants =
            maybe (emptyAt lo) id (spanOfNames (map Foil.nameId own))
        , storedLocals =
            maybe (emptyAt 0) id (spanOfNames (concat localIds))
        }
      ctx = envCtx env
      own =
        [ x
        | x <- Foil.nameSetToList (Foil.scopeToNameSet (ctxScope ctx))
        , lo <= Foil.nameId x, Foil.nameId x <= hi
        ]
      (decls, spellingsPer, localIds) = unzip3 (map declOf own)
      -- Only the referenced constants enter the table: it is hashed, so an
      -- unused import must not change the artifact, or content-defined
      -- early cutoff dies. See 'termSpellings'.
      spellings = Map.unions spellingsPer
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
                , adType       = storeTerm ty
                , adValue      = storeTerm value
                }
            , termSpellings (envDisplay env) ty
                <> termSpellings (envDisplay env) value
            , localsOf ty <> localsOf value )
   in ModuleArtifact
        { artifactModule  = name
        , artifactLayout  = layout
        , artifactSource  = source
        , artifactImports = imports
        , artifactHash    =
            contentHashBytes (runPut (put spellings <> put decls))
        , artifactSpellings = spellings
        , artifactDecls   = decls
        }

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
  relocation <-
    either (Left . located . renderArtifactError) Right $
      constantRelocation (artifactLayout artifact) range
                         (artifactSpellings artifact) (envDeclared env')
  go relocation (Blocks.beginBlock range) env' (artifactDecls artifact)
  where
    checkImport (m, h) = case Map.lookup m hashes of
      Just h' | h' == h -> Right ()
      Just _ -> Left (stale <> prettyVarIdent m <> " has changed since then")
      Nothing -> Left (stale <> prettyVarIdent m <> " is not among the modules loaded so far")
    stale = "stale artifact for " <> prettyVarIdent (artifactModule artifact) <> ": import "

    -- Locate an error at this artifact.
    located :: String -> ArtifactError
    located err =
      "artifact for " <> prettyVarIdent (artifactModule artifact) <> ": " <> err

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
      Nothing -> decode stored
      Just moved -> do
        t <- decode stored
        pure (Foil.sink (relocateConstants moved t))
      where
        decode :: forall o. StoredTerm -> Either ArtifactError (Term o)
        decode =
          either (Left . located . renderArtifactError) Right . decodeStored

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
