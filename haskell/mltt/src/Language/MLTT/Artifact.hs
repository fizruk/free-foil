{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Serialisation of checked modules.
--
-- A 'Foil.Name' is an allocation artefact and cannot be written to disk, so a
-- serialised declaration records /qualified spellings/ and is re-interned on
-- load: the artifact stores each declaration's type and value as raw syntax
-- in which every free variable is printed fully qualified (from 'envDisplay')
-- and every bound variable canonically (@l0@, @l1@, …). Loading parses the
-- terms back and converts them against the environment being assembled, so a
-- loaded module is an ordinary 'CheckedModule': it links, and further modules
-- check against it, exactly as if it had just been checked.
--
-- What makes the cache valid is recorded alongside the terms:
--
-- * the module's stripe index at check time, so a run whose registry agrees
--   reconstructs the very same raw names (and one whose registry moved the
--   stripe still loads, with the names landing where the new stripe says);
-- * the content hash of each import at check time, so a changed dependency
--   is detected and the artifact rejected rather than linked stale.
--
-- __Loading trusts the artifact's terms__: nothing is re-checked, which is
-- the point of a cache. Integrity comes from the hash chain, and the hash is
-- 'contentHash', a plain FNV-1a over the rendered content — collision
-- resistance enough for a build cache, not for an adversary.
--
-- Three wire-format notes:
--
-- * Bound variables are printed @l\<i\>@ from their raw ids; a program whose
--   fully qualified spelling matches that pattern would need escaping,
--   which this demo does not implement.
--
-- * Source positions inside a loaded term point into the artifact text, not
--   the original source.
--
-- * The bound spellings inherit the one place raw ids are not
--   deterministic: a λ-binder allocated during checking takes the successor
--   of the whole ambient scope's maximum, so its id — harmless in memory —
--   leaks into the artifact text, and the content hash is reproducible only
--   for a module checked in the same environment. The fix is for the
--   conversion layer to allocate the binders it introduces in a
--   caller-supplied region, not more code here.
module Language.MLTT.Artifact (
  ModuleArtifact (..),
  ArtifactDecl (..),
  ContentHash (..),
  StoredTerm (..),
  makeArtifact,
  loadArtifact,
  loadArtifactAfter,
  renderArtifact,
  readArtifact,
  contentHash,
) where

import qualified Control.Monad.Foil        as Foil
import qualified Control.Monad.Foil.Blocks as Blocks
import           Data.Bits                 (xor, (.&.))
import           Data.List                 (foldl')
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Text.Read                 (readEither)

import           Language.MLTT.Eval        (Def (..), desugar)
import           Language.MLTT.Impl
import           Language.MLTT.Impl.Generated
import           Language.MLTT.Resolve     (Visibility (..), prettyVarIdent)
import qualified Language.MLTT.Syntax.Abs  as Raw
import qualified Language.MLTT.Syntax.Lex  as Raw
import qualified Language.MLTT.Syntax.Par  as Raw
import           Language.MLTT.Typecheck   (Ctx (..), extend)

-- * The artifact

-- | A checked module, as written to disk.
data ModuleArtifact = ModuleArtifact
  { artifactModule  :: Raw.VarIdent  -- ^ The module's qualified name.
  , artifactStripe  :: StripeIndex   -- ^ From the registry, at check time.
  , artifactImports :: [(Raw.VarIdent, ContentHash)]
      -- ^ Each import, with its content hash at check time.
  , artifactHash    :: ContentHash   -- ^ Over the declarations below.
  , artifactDecls   :: [ArtifactDecl] -- ^ In declaration (= allocation) order.
  }
  deriving (Eq, Show, Read)

-- | One declaration: everything the environment needs to hold for it.
data ArtifactDecl = ArtifactDecl
  { adSpelling   :: Raw.VarIdent  -- ^ Fully qualified.
  , adVisibility :: Visibility
  , adType       :: StoredTerm
  , adValue      :: StoredTerm
  }
  deriving (Eq, Show, Read)

-- | A term as stored: raw syntax with fully qualified free variables and
-- canonically named bound ones.
newtype StoredTerm = StoredTerm { storedText :: String }
  deriving (Eq, Show, Read)

-- | The 64-bit FNV-1a of some rendered content; see 'contentHash'.
newtype ContentHash = ContentHash Integer
  deriving (Eq, Show, Read)

-- | Render an artifact for writing. 'readArtifact' is its inverse.
renderArtifact :: ModuleArtifact -> String
renderArtifact = show

-- | Read an artifact back; reports rather than crashes on malformed input.
readArtifact :: String -> Either String ModuleArtifact
readArtifact = readEither

-- | FNV-1a over a string, 64 bits. A build-cache checksum, not a defence.
contentHash :: String -> ContentHash
contentHash = ContentHash . foldl' step 0xcbf29ce484222325
  where
    step h c = ((h `xor` fromIntegral (fromEnum c)) * 0x100000001b3) .&. 0xffffffffffffffff

-- * Writing

-- | Serialise a checked module.
--
-- The declarations are exactly the names the module allocated in its stripe,
-- in ascending order, which is declaration order; their spellings come from
-- 'envDisplay' and are fully qualified, so the artifact does not depend on
-- what was visible under which shorter spelling at check time.
makeArtifact
  :: Raw.VarIdent               -- ^ The module's name.
  -> StripeIndex                -- ^ From the registry.
  -> [(Raw.VarIdent, ContentHash)] -- ^ Its imports, with their content hashes.
  -> CheckedModule c
  -> ModuleArtifact
makeArtifact name stripe imports cm = withCheckedModule cm $ \_ env _ ->
  let Foil.NameRange lo hi = stripeRange stripe
      ctx = envCtx env
      own =
        [ x
        | x <- Foil.nameSetToList (Foil.scopeToNameSet (ctxScope ctx))
        , lo <= Foil.nameId x, Foil.nameId x <= hi
        ]
      decls = map declOf own
      declOf x = ArtifactDecl
        { adSpelling   = spelling
        , adVisibility = if Map.member spelling (envExports env) then Public else Private
        , adType       = put (Foil.lookupName x (ctxTypes ctx))
        , adValue      = case getDef (Foil.lookupName x (ctxDefs ctx)) of
            Just value -> put value
            Nothing    -> error "impossible: a top-level name with no definition"
        }
        where
          spelling = Foil.lookupName x (envDisplay env)
      put = StoredTerm . showTermNamed boundName (envDisplay env)
   in ModuleArtifact
        { artifactModule  = name
        , artifactStripe  = stripe
        , artifactImports = imports
        , artifactHash    = contentHash (concatMap renderDecl decls)
        , artifactDecls   = decls
        }

-- | The canonical spelling of a bound variable in an artifact.
boundName :: Int -> Raw.VarIdent
boundName i = Raw.VarIdent ("l" <> show i)

-- | What the content hash covers: everything semantically relevant. The
-- values are included, not only the types, because conversion unfolds
-- definitions, so a changed body changes what dependants compute.
renderDecl :: ArtifactDecl -> String
renderDecl d = unwords
  [ prettyVarIdent (adSpelling d), show (adVisibility d)
  , storedText (adType d), storedText (adValue d), ";"
  ]

-- * Loading

-- | Load a checked module from its artifact, into an environment holding
-- what its imports export — the same starting point 'checkModule' has.
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
  -> Either String (CheckedModule c)
loadArtifact hashes range env artifact = do
  mapM_ checkImport (artifactImports artifact)
  go (Blocks.beginBlock range) env' (artifactDecls artifact)
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

    go :: Foil.DExt c n
       => Blocks.Block c n -> Env n -> [ArtifactDecl] -> Either String (CheckedModule c)
    go block envN [] =
      Right (CheckedModule (Blocks.blockExt block)
                           (finishModule (artifactModule artifact) envN)
                           [])
    go block envN (d : ds) = do
      ty    <- reintern envN (adType d)
      value <- reintern envN (adValue d)
      Blocks.withFreshInBlock block (ctxScope (envCtx envN)) $ \binder block' ->
        let ctx' = extend (envCtx envN) binder ty (Just value)
            envN' = extendEnv ctx' binder (adSpelling d) (adVisibility d) envN
         in go block' envN' ds

    -- Parse a stored term and convert it against the environment assembled
    -- so far: this is the re-interning the wire format promises.
    reintern :: Foil.Distinct n => Env n -> StoredTerm -> Either String (Term n)
    reintern envN (StoredTerm input) = do
      raw <- Raw.pTerm (Raw.tokens input)
      case tryToTerm' (ctxScope (envCtx envN)) (envDeclared envN) raw of
        Left err -> Left ("artifact for " <> prettyVarIdent (artifactModule artifact)
                            <> ": " <> notInScope err)
        Right t  -> Right (desugar t)

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
  -> Either String (CheckedModule c)
loadArtifactAfter hashes range (CheckedModule ext env results) artifact = do
  cm <- loadArtifact hashes range env artifact
  case cm of
    CheckedModule ext' env' results' ->
      Right (CheckedModule (Blocks.composeExtWithin ext ext') env' (results <> results'))
