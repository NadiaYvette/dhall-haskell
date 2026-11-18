{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}

-- |
-- Module      : Dhall.Import.Penelope
-- Description : Polytropos.Core.Rep flat Dhall records and StaticPenelope import scheduler.
--
-- Completes Depth 3 of the Dhall acceleration architecture:
--
--   1. Replaces pointer-heavy @Dhall.Map.Map Text Expr@ trees with 'FlatRecord',
--      pairing an interned 'SchemaId' with a contiguous 'Polytropos.Core.Rep' payload array.
--   2. Extracts all transitive @env:@, local file, and HTTP imports statically
--      before CESK evaluation begins ('ImportFootprint') and partitions the
--      deduplicated dependency DAG into concurrent topological execution waves.
module Dhall.Import.Penelope
  ( FlatRecord(..)
  , ImportKey(..)
  , ImportFootprint(..)
  , StaticImportDag(..)
  , mkFlatRecord
  , lookupFlatRecord
  , mergeFlatRecords
  , extractImportFootprint
  , scheduleParallelImportWaves
  ) where

import Data.Functor.Identity (Identity(..))
import qualified Data.Map.Strict as Map
import Data.Primitive.PrimArray
  ( PrimArray
  , indexPrimArray
  , sizeofPrimArray
  )
import Data.Primitive.SmallArray
  ( indexSmallArray
  , sizeofSmallArray
  , smallArrayFromList
  )
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Word (Word32)
import GHC.Exts (unsafeCoerce#)

import Polytropos.Core (Rep(..))
import Pykinos.Schema.HiddenClass
  ( FieldId(..)
  , MergeMorph3(..)
  , RecordOp(..)
  , SchemaId(..)
  , decodeMergeCode3
  , findFieldSlot
  , synthesizeMergeMorph3
  )

-- | A flat Dhall record or union alternative table backed directly by
--   'Polytropos.Core.Rep' and an interned 'Pykinos.Schema.HiddenClass.SchemaId'.
--   Eliminates O(F log F) tree lookups and enables zero-copy marshalling into
--   static Polytropos 'Record' types at the 'FromDhall' boundary.
data FlatRecord a = FlatRecord
  { frSchemaId :: {-# UNPACK #-} !SchemaId
    -- ^ Interned schema identifier defining field ordering and offsets.
  , frRep      :: !(Rep Identity a)
    -- ^ Contiguous array payload matching the schema slots.
  }

instance Functor FlatRecord where
  -- | Functor map over record values preserving structural schema layout.
  fmap f (FlatRecord sid (Rep tag arr)) =
    let !n = sizeofSmallArray arr
        !arr' = smallArrayFromList
          [ let Identity x = unsafeCoerce# (indexSmallArray arr i)
            in unsafeCoerce# (Identity (f x))
          | i <- [0 .. n - 1]
          ]
    in FlatRecord sid (Rep tag arr')

-- | Construct a 'FlatRecord' from a 'SchemaId' and a sorted list of field values.
-- Pack each element under Identity into the contiguous payload array.
{-# INLINE mkFlatRecord #-}
mkFlatRecord :: SchemaId -> [a] -> FlatRecord a
mkFlatRecord !sid xs =
  let !arr = smallArrayFromList [unsafeCoerce# (Identity x) | x <- xs]
  in FlatRecord sid (Rep 0 arr)

-- | Lookup a field in a 'FlatRecord' in O(log_2 F) unboxed binary search
--   followed by an O(1) 'indexSmallArray' pointer read.
{-# INLINE lookupFlatRecord #-}
lookupFlatRecord
  :: (SchemaId -> PrimArray Word32)
  -> FieldId
  -> FlatRecord a
  -> Maybe a
lookupFlatRecord getSchema !fid (FlatRecord !sid (Rep _ !arr)) =
  case findFieldSlot (getSchema sid) fid of
    Nothing     -> Nothing
    Just slotIx ->
      -- Direct unboxed slot dereference:
      let Identity val = unsafeCoerce# (indexSmallArray arr slotIx)
      in Just val

-- | Merge two 'FlatRecord' structures using a 3-way 'MergeMorph3' plan
--   ('OpPreferR' for @//@, 'OpCombineDeep' for @/\\@, or 'OpRestrict' for @|<@).
-- Synthesizes the output schema and executes the compiled shuffle plan in a single pass.
{-# INLINE mergeFlatRecords #-}
mergeFlatRecords
  :: (SchemaId -> PrimArray Word32)
  -> (PrimArray Word32 -> SchemaId)
  -> RecordOp
  -> (a -> a -> a)
  -> FlatRecord a
  -> FlatRecord a
  -> FlatRecord a
mergeFlatRecords getSchema internSchema !op onCollision
  (FlatRecord !sid1 (Rep _ !arr1))
  (FlatRecord !sid2 (Rep _ !arr2)) =
  let (!fOut, MergeMorph3 !plan) =
        synthesizeMergeMorph3 op (getSchema sid1) (getSchema sid2)
      !sidOut = internSchema fOut
      !nOut   = sizeofPrimArray plan
      !outArr = smallArrayFromList
        [ case decodeMergeCode3 (indexPrimArray plan i) of
            Left (Left idx1)  -> indexSmallArray arr1 idx1
            Left (Right idx2) -> indexSmallArray arr2 idx2
            Right (idx1, idx2) ->
              let Identity v1 = unsafeCoerce# (indexSmallArray arr1 idx1)
                  Identity v2 = unsafeCoerce# (indexSmallArray arr2 idx2)
              in unsafeCoerce# (Identity (onCollision v1 v2))
        | i <- [0 .. nOut - 1]
        ]
  in FlatRecord sidOut (Rep 0 outArr)

-- | Canonical content-addressed or location-addressed identifier for a Dhall import.
data ImportKey
  = ImportEnv    !Text
    -- ^ @env:VAR@ startup coeffect
  | ImportLocal  !Text !(Maybe Text)
    -- ^ Normalized file path + optional @sha256:...@ integrity hash
  | ImportRemote !Text !(Maybe Text)
    -- ^ Canonical URL + optional @sha256:...@ integrity hash
  deriving (Eq, Ord, Show)

-- | Cayley-accumulated static footprint of an un-evaluated Dhall AST,
--   separating fast local/environment coeffects from network I/O imports.
data ImportFootprint = ImportFootprint
  { ifEnvVars    :: !(Set.Set Text)
  , ifLocalFiles :: !(Set.Set ImportKey)
  , ifRemoteUrls :: !(Set.Set ImportKey)
  }
  deriving (Eq, Show)

instance Semigroup ImportFootprint where
  ImportFootprint e1 l1 r1 <> ImportFootprint e2 l2 r2 =
    ImportFootprint (Set.union e1 e2) (Set.union l1 l2) (Set.union r1 r2)

instance Monoid ImportFootprint where
  mempty = ImportFootprint Set.empty Set.empty Set.empty

-- | Extract the static 'ImportFootprint' from any foldable AST container of 'ImportKey's
--   in a single pass before invoking the CESK normalizer.
extractImportFootprint :: Foldable t => t ImportKey -> ImportFootprint
extractImportFootprint = foldr insertKey mempty
  where
    insertKey key@ImportEnv{} acc =
      case key of
        ImportEnv var -> acc { ifEnvVars = Set.insert var (ifEnvVars acc) }
        _             -> acc
    insertKey key@ImportLocal{} acc =
      acc { ifLocalFiles = Set.insert key (ifLocalFiles acc) }
    insertKey key@ImportRemote{} acc =
      acc { ifRemoteUrls = Set.insert key (ifRemoteUrls acc) }

-- | Deduplicated transitive import dependency graph mapping each 'ImportKey'
--   to the set of child 'ImportKey's it directly imports.
newtype StaticImportDag = StaticImportDag
  { unStaticImportDag :: Map.Map ImportKey (Set.Set ImportKey) }
  deriving newtype (Eq, Show)

-- | Partition a 'StaticImportDag' into bottom-up topological waves of mutually
--   independent imports. Every 'ImportKey' in wave @k@ depends only on imports
--   already resolved and cached in waves @0 .. k - 1@, enabling 'Penelope'
--   multi-region handlers to fetch and normalize each wave in parallel.
scheduleParallelImportWaves :: StaticImportDag -> [[ImportKey]]
scheduleParallelImportWaves (StaticImportDag dagMap) =
  let allNodes = Map.keysSet dagMap `Set.union` Set.unions (Map.elems dagMap)
      -- Normalize adjacency map so leaf imports with 0 dependencies are present:
      fullDag  = Map.fromSet (\k -> Map.findWithDefault Set.empty k dagMap) allNodes
      peelWaves !remaining
        | Map.null remaining = []
        | otherwise =
            let readyMap = Map.filter Set.null remaining
                readySet = Map.keysSet readyMap
            in if Set.null readySet
                 then
                   -- Cyclic import fallback: emit remaining keys in deterministic order
                   [Set.toAscList (Map.keysSet remaining)]
                 else
                   let !wave = Set.toAscList readySet
                       !nextRemaining =
                         Map.map (`Set.difference` readySet)
                           (remaining `Map.withoutKeys` readySet)
                   in wave : peelWaves nextRemaining
  in peelWaves fullDag
