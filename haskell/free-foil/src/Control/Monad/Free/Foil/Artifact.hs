{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Serialisation support for checked units: stored terms, spelling tables,
-- name-range metadata, and relocation.
--
-- The machinery here assumes only that a unit's /interned constants/ and
-- its /locals/ (the names its binders bind) occupy disjoint name ranges,
-- and it checks that assumption from the recorded metadata rather than
-- taking it on faith. A stored term is then meaningful verbatim: a local
-- keeps its raw id, and a constant is resolved through a spelling table on
-- load. The never-cross-zero layout — constants below zero, locals at or
-- above — is one policy that provides the disjointness globally and by
-- construction; it is what the guarded successor allocator protects, and
-- what the @mltt@ package in the free-foil repository uses, as the worked
-- example of a full artifact built from these parts.
--
-- What loading trusts, and what it checks, is the client's decision; the
-- functions here supply the checkable facts. 'checkStoredLayout' judges the
-- recorded ranges, 'constantRelocation' judges the constants, and both
-- judge from metadata alone, so no stored term is ever walked for
-- checking. Only 'relocateConstants' walks a term, and only when a
-- constant actually moved.
module Control.Monad.Free.Foil.Artifact (
  -- * Errors
  ArtifactError (..),
  prettyArtifactError,
  -- * Stored terms
  StoredTerm (..),
  storeTerm,
  decodeStored,
  -- * Spelling tables and locals
  termSpellings,
  localsOf,
  spanOfNames,
  -- * Range metadata and its checks
  StoredLayout (..),
  nameRangeSize,
  nameRangeContains,
  nameRangesOverlap,
  checkStoredLayout,
  -- * Relocation
  constantRelocation,
  relocateConstants,
) where

import           Data.Binary                    (Binary, get)
import qualified Data.Binary                    as Binary
import           Data.Binary.Get                (runGetOrFail)
import           Data.Bifoldable                (Bifoldable, bifoldMap)
import           Data.Bifunctor                 (Bifunctor, bimap)
import qualified Data.ByteString.Lazy           as BSL
import qualified Data.IntMap                    as IntMap
import qualified Data.IntSet                    as IntSet
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           GHC.Generics                   (Generic)
import           Unsafe.Coerce                  (unsafeCoerce)

import           Control.Monad.Foil.Internal
import           Control.Monad.Free.Foil        (AST (..), ScopedAST (..),
                                                 supportOf)
import           Control.Monad.Free.Foil.Binary ()

-- $setup
-- >>> import Control.Monad.Foil (NameRange (..))
-- >>> import qualified Data.Map as Map

-- * Errors

-- | What the machinery here can report. The type is parametric in the
-- spelling, as the tables are, and a 'Functor' over it.
data ArtifactError ident
  = MalformedStoredTerm String
      -- ^ The bytes did not decode; the message is the decoder's.
  | OverlappingRegions NameRange NameRange
      -- ^ The recorded constants and locals ranges share a name.
  | SpellingForLocal RawName
      -- ^ The spelling table names something inside the locals region.
  | WrongDeclarationCount NameRange Int
      -- ^ The constants range does not hold one name per declaration.
  | UnknownConstant ident
      -- ^ A spelling the loading world does not know.
  | ConstantAmongLocals ident RawName
      -- ^ A relocation target inside the locals region, where the verbatim
      -- locals could capture it.
  deriving (Eq, Show, Functor)

-- | Render an error, given a renderer for the spellings.
prettyArtifactError :: (ident -> String) -> ArtifactError ident -> String
prettyArtifactError prettyIdent = \case
  MalformedStoredTerm msg -> "malformed stored term: " <> msg
  OverlappingRegions _ _ -> "the constants and locals regions overlap"
  SpellingForLocal i -> "a spelling for local " <> show i
  WrongDeclarationCount range count ->
    "the constants range holds " <> show (nameRangeSize range)
      <> " names for " <> show count <> " declarations"
  UnknownConstant x -> "not in scope: " <> prettyIdent x
  ConstantAmongLocals x _ ->
    "constant " <> prettyIdent x <> " would land in the locals region"

-- * Stored terms

-- | A term as stored: canonical bytes. Equality of stored terms is byte
-- equality, which is what a canonical-artifact property tests.
newtype StoredTerm = StoredTerm { storedBytes :: BSL.ByteString }
  deriving (Eq, Show, Generic, Binary)

-- | Store a term verbatim, through the instances of
-- "Control.Monad.Free.Foil.Binary".
--
-- The disjoint layout is what makes verbatim enough. A constant's spelling
-- goes into the unit's table ('termSpellings'), and a local needs no
-- table: its id is expected to be canonical, which it is when elaboration
-- allocates locals in a region of their own.
storeTerm :: Binary (AST binder sig n) => AST binder sig n -> StoredTerm
storeTerm = StoredTerm . Binary.encode

-- | Decode a stored term's bytes: the instances alone, no meaning yet.
-- Meaning is given per unit, by 'constantRelocation' and
-- 'relocateConstants'.
decodeStored
  :: Binary (AST binder sig n)
  => StoredTerm -> Either (ArtifactError ident) (AST binder sig n)
decodeStored (StoredTerm bytes) =
  case runGetOrFail get bytes of
    Left (_, _, err) -> Left (MalformedStoredTerm err)
    Right (rest, _, term)
      | not (BSL.null rest) -> Left (MalformedStoredTerm "trailing bytes")
      | otherwise -> Right term

-- * Spelling tables and locals

-- | The spelling-table entries a term needs. Its free variables are exactly
-- its constants, provided the stored declaration is closed over everything
-- local; each is mapped to its spelling from the display table.
--
-- Note that the table should cover the referenced constants and only
-- those. A table of everything in scope would let an unused import dirty a
-- dependant's content hash, and would differ between build schedules.
termSpellings
  :: (Distinct n, CoSinkable binder, Bifoldable sig)
  => NameMap n ident      -- ^ Spellings of the top-level names.
  -> AST binder sig n
  -> Map RawName ident
termSpellings display t = Map.fromList
  [ (nameId x, lookupName x display)
  | x <- nameSetToList (supportOf t)
  ]

-- | The names a term's binders bind: what a unit's locals range covers.
-- Note that 'supportOf' cannot see them; they are bound, not free.
localsOf
  :: (Bifoldable sig, HasNameBinders binder)
  => AST binder sig n -> [RawName]
localsOf = \case
  Var _    -> []
  Node sig -> bifoldMap scopedLocals localsOf sig
  where
    scopedLocals (ScopedAST pat body) =
      binderNames pat <> localsOf body
    binderNames pat = case getNameBinders pat of
      UnsafeNameBinders ids -> IntSet.toList ids

-- | The tightest range covering the given names, or 'Nothing' for none.
-- The caller picks its own convention for the empty range.
--
-- >>> spanOfNames [7, 3, 5]
-- Just (NameRange {nameRangeLo = 3, nameRangeHi = 7})
spanOfNames :: [RawName] -> Maybe NameRange
spanOfNames [] = Nothing
spanOfNames ids = Just (NameRange (minimum ids) (maximum ids))

-- * Range metadata and its checks

-- | A unit's recorded name layout: the actual names of its own constants,
-- and of its locals. The two travel together — an artifact records them as
-- one field, and the checks and the relocation consume them as one value —
-- so they cannot be mixed up with the ranges of the loading world.
data StoredLayout = StoredLayout
  { storedConstants :: NameRange
  , storedLocals    :: NameRange
  }
  deriving (Eq, Show, Generic, Binary)

-- | How many names a range holds.
--
-- >>> nameRangeSize (NameRange 3 5)
-- 3
nameRangeSize :: NameRange -> Int
nameRangeSize (NameRange lo hi) = max 0 (hi - lo + 1)

-- | Whether a raw name lies in a range.
nameRangeContains :: NameRange -> RawName -> Bool
nameRangeContains (NameRange lo hi) i = lo <= i && i <= hi

-- | Whether two ranges share a name. An empty range overlaps nothing.
--
-- >>> nameRangesOverlap (NameRange 0 4) (NameRange 4 9)
-- True
-- >>> nameRangesOverlap (NameRange 0 4) (NameRange 5 9)
-- False
nameRangesOverlap :: NameRange -> NameRange -> Bool
nameRangesOverlap (NameRange lo1 hi1) (NameRange lo2 hi2) =
  lo1 <= hi1 && lo2 <= hi2 && lo1 <= hi2 && lo2 <= hi1

-- | The checks a unit's recorded layout admits, judged from metadata alone.
-- The constants and locals ranges must not overlap; no spelling may be
-- recorded for a local; and the constants range must hold exactly one name
-- per declaration, since allocation is dense from the range's low end.
--
-- >>> layout = StoredLayout (NameRange (-10) (-9)) (NameRange 0 5)
-- >>> checkStoredLayout layout (Map.fromList [(-20, "P.base")]) 2
-- Right ()
-- >>> checkStoredLayout layout (Map.fromList [(3, "q")]) 2
-- Left (SpellingForLocal 3)
checkStoredLayout
  :: StoredLayout         -- ^ The unit's recorded layout.
  -> Map RawName ident    -- ^ Its spelling table.
  -> Int                  -- ^ Its declaration count.
  -> Either (ArtifactError ident) ()
checkStoredLayout (StoredLayout constants locals) table declCount
  | nameRangesOverlap constants locals =
      Left (OverlappingRegions constants locals)
  | (i : _) <- filter (nameRangeContains locals) (Map.keys table) =
      Left (SpellingForLocal i)
  | nameRangeSize constants /= declCount =
      Left (WrongDeclarationCount constants declCount)
  | otherwise = Right ()

-- * Relocation

-- | What a unit's constants need in the loading world, judged once, from
-- the spelling table alone. 'Nothing' says every constant already has the
-- id its spelling means here; this is the fast path, on which no term is
-- walked at all. Otherwise the result is the renaming to apply. Its domain
-- is a scope of the unit's world, which no longer exists, so its index is
-- the caller's phantom.
--
-- The unit's own constants (table entries inside the recorded range) do
-- not consult the world: they are being loaded right now, in the same
-- order they were allocated, so their relocation is the affine shift
-- between the recorded range and the one this run assigned. Their new
-- names are thereby minted ahead of their allocation, which the caller's
-- trust covers. An imported constant resolves by its spelling; one this
-- world does not know is reported. Finally, no relocation target may land
-- among the locals, since verbatim locals rest on the two never meeting.
constantRelocation
  :: Ord ident
  => StoredLayout         -- ^ The unit's recorded layout.
  -> NameRange            -- ^ The range this run assigned to the unit.
  -> Map RawName ident    -- ^ Its spelling table.
  -> Map ident (Name n')  -- ^ What each spelling means here.
  -> Either (ArtifactError ident) (Maybe (NameMap old (Name n')))
constantRelocation (StoredLayout old locals) (NameRange newLo _) table globals = do
  entries <- Map.foldrWithKey step (Right []) table
  pure $
    if any (\(i, name) -> nameId name /= i) entries
      then Just (NameMap (IntMap.fromList entries))
      else Nothing
  where
    NameRange oldLo _ = old
    shift = newLo - oldLo
    step i spelling acc = do
      rest <- acc
      name <-
        if nameRangeContains old i
          then Right (UnsafeName (i + shift))
          else case Map.lookup spelling globals of
            Nothing   -> Left (UnknownConstant spelling)
            Just name -> Right name
      if nameRangeContains locals (nameId name)
        then Left (ConstantAmongLocals spelling (nameId name))
        else pure ((i, name) : rest)

-- | Rename every constant reference through the map, moving the term from
-- the unit's world into the loading one. This is the restriction to
-- constants of a general renaming @'Name' n -> 'Name' n'@.
-- 'sinkabilityProof' embodies the general renaming, but its efficient
-- implementations degenerate the renaming to a coercion under binders,
-- which is sound only for inclusions; this walk carries an arbitrary map
-- through.
--
-- The invariant that lets the walk ignore the binders is the disjointness
-- the recorded layout certifies: every name in the map's domain is a
-- constant, and a binder binds locals, so no binder can shadow a name in
-- the domain and no local can be in it. Note that this covers imported
-- constants too, since 'checkStoredLayout' refuses a spelling for any name
-- among the locals. Thus the map never needs extending under a binder, and
-- locals and patterns cross by coercion. A constant outside the map (bytes
-- referencing something the spelling table does not cover) is re-minted
-- unchanged, trusted like everything else about the term. Note that a map
-- that is the identity on raw ids would make the whole walk a coercion,
-- which is why 'constantRelocation' reports it as no relocation at all.
relocateConstants
  :: forall binder sig n n'. Bifunctor sig
  => NameMap n (Name n') -> AST binder sig n -> AST binder sig n'
relocateConstants (NameMap moved) = walk
  where
    walk :: forall o o'. AST binder sig o -> AST binder sig o'
    walk = \case
      Var x -> case IntMap.lookup (nameId x) moved of
        Just new -> Var (UnsafeName (nameId new))
        Nothing  -> Var (UnsafeName (nameId x))
      Node sig -> Node (bimap walkScoped walk sig)

    walkScoped :: forall o o'. ScopedAST binder sig o -> ScopedAST binder sig o'
    walkScoped (ScopedAST pat body) = ScopedAST (unsafeCoerce pat) (walk body)
