{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- |
-- Module      : Dhall.Eval.CEK.HashCons
-- Description : SwissTable128-backed normal-form DAG arena with O(1) alpha-beta equality.
--
-- Replaces syntactic tree readback during Dhall normalization and typechecking
-- with a hash-consed Normal Form Arena ('NfArena'). Because binder variables are
-- canonicalized to De Bruijn indices before interning into 'SwissTable128':
--
--   1. Judgmental equality (@alpha-beta@ equivalence) reduces to O(1) integer
--      comparison ('judgmentallyEqualNf') on 'Int32' 'NfAddr' identifiers.
--   2. Semantic integrity hashing computes 256-bit Merkle digests bottom-up in
--      strictly O(|DAG|) time without expanding shared sub-DAGs into trees.
module Dhall.Eval.CEK.HashCons
  ( Digest256(..)
  , NfArena(..)
  , pattern NT_Lit
  , pattern NT_Var
  , pattern NT_Lam
  , pattern NT_Pi
  , pattern NT_App
  , pattern NT_Proj
  , pattern NT_PreferR
  , pattern NT_CombineDeep
  , pattern NT_RecordNil
  , pattern NT_RecordCons
  , pattern NT_RecordRoot
  , newNfArena
  , internNfLit
  , internNfDeBruijnVar
  , internNfBinder
  , internNfApp
  , internNfProj
  , internNfMerge
  , internNfRecord
  , readNfDigest256
  , judgmentallyEqualNf
  ) where

import Control.Monad.ST (ST)
import Data.Bits (rotateL, unsafeShiftR, xor)
import Data.Int (Int32)
import Data.Primitive.ByteArray
  ( MutableByteArray
  , newByteArray
  , readByteArray
  , writeByteArray
  )
import Data.Primitive.SmallArray
  ( SmallArray
  , indexSmallArray
  , sizeofSmallArray
  )
import Data.Word (Word8, Word32, Word64)

import Pykinos.Mutable.SwissTable
  ( SwissTable128
  , lookupOrInsert128
  , newSwissTable128
  , packNfNode128
  )
import Pykinos.Schema.HiddenClass
  ( FieldId(..)
  , RecordOp(..)
  , SchemaId(..)
  )

-- | 1-byte normal-form DAG opcode tags for 'packNfNode128'.
-- Lit tag identifies integer and scalar literals.
pattern NT_Lit         :: Word8
pattern NT_Lit         = 1

-- | Var tag identifies de Bruijn index variables.
pattern NT_Var         :: Word8
pattern NT_Var         = 2

-- | Lam tag identifies lambda abstraction nodes.
pattern NT_Lam         :: Word8
pattern NT_Lam         = 3

-- | Pi tag identifies dependent function types (Pi).
pattern NT_Pi          :: Word8
pattern NT_Pi          = 4

-- | App tag identifies function application nodes.
pattern NT_App         :: Word8
pattern NT_App         = 5

-- | Proj tag identifies record field projection.
pattern NT_Proj        :: Word8
pattern NT_Proj        = 6

-- | PreferR tag identifies right-biased record overrides (//@).
pattern NT_PreferR     :: Word8
pattern NT_PreferR     = 7

-- | CombineDeep tag identifies recursive record combinations (/\\@).
pattern NT_CombineDeep :: Word8
pattern NT_CombineDeep = 8

-- | RecordNil tag identifies empty record terminal spine.
pattern NT_RecordNil   :: Word8
pattern NT_RecordNil   = 9

-- | RecordCons tag identifies record field cons cells.
pattern NT_RecordCons  :: Word8
pattern NT_RecordCons  = 10

-- | RecordRoot tag identifies root record header with schema ID.
pattern NT_RecordRoot  :: Word8
pattern NT_RecordRoot  = 11

-- | Unboxed 256-bit (32-byte) Merkle digest for O(|DAG|) semantic hashing.
data Digest256 = Digest256
  { d256_0 :: {-# UNPACK #-} !Word64
  , d256_1 :: {-# UNPACK #-} !Word64
  , d256_2 :: {-# UNPACK #-} !Word64
  , d256_3 :: {-# UNPACK #-} !Word64
  }
  deriving (Eq, Ord, Show)

-- | Hash-consed Normal Form Arena backed by 'SwissTable128' and an unboxed
--   256-bit Merkle digest slab ('nfaDigests').
--   Contains zero boxed pointers so GHC's garbage collector never scans it.
data NfArena s = NfArena
  { nfaTable   :: !(SwissTable128 s)
    -- ^ Maps 128-bit packed 'NfNode' keys to dense monotonic 'Int32' 'NfAddr's.
  , nfaDigests :: !(MutableByteArray s)
    -- ^ Unboxed slab of @cap * 32@ bytes storing 'Digest256' per 'NfAddr'.
  , nfaState   :: !(MutableByteArray s)
    -- ^ Int32[0] = highest 'NfAddr' whose Merkle digest has been initialized.
  }

-- | Allocate a fresh 'NfArena' with pre-allocated 'SwissTable128' and digest slab.
-- The initial capacity is clamped to a minimum of 1024 slots to ensure ample headroom.
newNfArena :: Int -> ST s (NfArena s)
newNfArena !initCap = do
  let !cap = max 1024 initCap
  -- Allocate the zero-GC SWAR SwissTable with 128-bit SIMD key layout:
  tbl  <- newSwissTable128 cap
  -- Allocate unboxed 32-byte digest slice per capacity entry:
  digs <- newByteArray (cap * 32)
  -- Allocate 4-byte high-water tracking word:
  st   <- newByteArray 4
  -- Initialize high-water digest index to -1:
  writeByteArray st 0 (-1 :: Int32)
  pure (NfArena tbl digs st)

-- | Read the 256-bit Merkle digest of an already-interned 'NfAddr' in O(1) time.
-- Directly indexing the unboxed 'nfaDigests' array across four Word64 slots.
{-# INLINE readNfDigest256 #-}
readNfDigest256 :: NfArena s -> Int32 -> ST s Digest256
readNfDigest256 NfArena{..} !nfAddr = do
  let !base = fromIntegral nfAddr * 4
  -- Read four consecutive 64-bit limbs:
  !w0 <- readByteArray nfaDigests (base + 0)
  !w1 <- readByteArray nfaDigests (base + 1)
  !w2 <- readByteArray nfaDigests (base + 2)
  !w3 <- readByteArray nfaDigests (base + 3)
  pure (Digest256 w0 w1 w2 w3)

-- | Incremental SipHash/SplitMix-style 256-bit sponge permutation combining a
--   128-bit structural key @(kLo, kHi)@ with up to two child 'NfAddr' digests.
-- Skips recomputation if the node's digest was already finalized.
{-# INLINE computeAndStoreDigest #-}
computeAndStoreDigest
  :: NfArena s
  -> Int32
  -> Word64
  -> Word64
  -> Int32
  -> Int32
  -> ST s ()
computeAndStoreDigest arena@NfArena{..} !nfAddr !kLo !kHi !childA !childB = do
  highWater :: Int32 <- readByteArray nfaState 0
  if nfAddr <= highWater
    then pure ()
    else do
      -- Resolve digest for left child (or fallback seed):
      Digest256 a0 a1 a2 a3 <-
        if childA >= 0
          then readNfDigest256 arena childA
          else pure (Digest256 0x736F6D6570736575 0x646F72616E646F6D 0x6C7967656E657261 0x7465646279746573)
      -- Resolve digest for right child (or fallback golden-ratio seed):
      Digest256 b0 b1 b2 b3 <-
        if childB >= 0
          then readNfDigest256 arena childB
          else pure (Digest256 0x9E3779B97F4A7C15 0xBF58476D1CE4E5B9 0x94D049BB133111EB 0x2545F4914F6CDD1D)
      -- Apply 4-lane SplitMix round permutation:
      let !m0 = mix64 (a0 `xor` kLo) (b0 `rotateL` 13)
          !m1 = mix64 (a1 `xor` kHi) (b1 `rotateL` 29)
          !m2 = mix64 (a2 `xor` m0)  (b2 `rotateL` 41)
          !m3 = mix64 (a3 `xor` m1)  (b3 `rotateL` 53)
          !base = fromIntegral nfAddr * 4
      -- Store 256-bit computed digest back into unboxed byte array:
      writeByteArray nfaDigests (base + 0) m0
      writeByteArray nfaDigests (base + 1) m1
      writeByteArray nfaDigests (base + 2) m2
      writeByteArray nfaDigests (base + 3) m3
      writeByteArray nfaState 0 nfAddr
  where
    -- | 64-bit SplitMix avalanche mixer with high non-linearity.
    {-# INLINE mix64 #-}
    mix64 :: Word64 -> Word64 -> Word64
    mix64 !x !y =
      let !z0 = (x + y) * 0xBF58476D1CE4E5B9
          !z1 = (z0 `xor` (z0 `unsafeShiftR` 30)) * 0x94D049BB133111EB
      in z1 `xor` (z1 `unsafeShiftR` 31)

-- | Intern a packed 128-bit node and ensure its 256-bit Merkle digest is recorded.
{-# INLINE internPackedNode #-}
internPackedNode
  :: NfArena s
  -> Word8
  -> Word32
  -> Int32
  -> Int32
  -> Int32
  -> ST s Int32
internPackedNode arena@NfArena{..} !tag !aux !cA !cB !cC = do
  let (!kLo, !kHi) = packNfNode128 tag aux cA cB cC
  !nfAddr <- lookupOrInsert128 nfaTable kLo kHi
  computeAndStoreDigest arena nfAddr kLo kHi cA cB
  pure nfAddr

-- | Intern a primitive integer literal node into 'NfArena'.
{-# INLINE internNfLit #-}
internNfLit :: NfArena s -> Int32 -> ST s Int32
internNfLit !arena !litVal =
  internPackedNode arena NT_Lit 0 litVal (-1) (-1)

-- | Intern a canonical De Bruijn index variable node into 'NfArena'.
--   Because variables use canonical De Bruijn indices rather than raw 'SymId's,
--   alpha-equivalent binders produce identical 'NfAddr's.
{-# INLINE internNfDeBruijnVar #-}
internNfDeBruijnVar :: NfArena s -> Int32 -> ST s Int32
internNfDeBruijnVar !arena !deBruijnIx =
  internPackedNode arena NT_Var 0 deBruijnIx (-1) (-1)

-- | Intern a lambda ('NT_Lam') or Pi ('NT_Pi') binder with normalized domain and body.
{-# INLINE internNfBinder #-}
internNfBinder :: NfArena s -> Bool -> Int32 -> Int32 -> ST s Int32
internNfBinder !arena !isPi !domNf !bodyNf =
  let !tag = if isPi then NT_Pi else NT_Lam
  in internPackedNode arena tag 0 domNf bodyNf (-1)

-- | Intern a function application node @(fnNf argNf)@.
{-# INLINE internNfApp #-}
internNfApp :: NfArena s -> Int32 -> Int32 -> ST s Int32
internNfApp !arena !fnNf !argNf =
  internPackedNode arena NT_App 0 fnNf argNf (-1)

-- | Intern a record field projection node @(recNf . fieldId)@.
{-# INLINE internNfProj #-}
internNfProj :: NfArena s -> Int32 -> FieldId -> ST s Int32
internNfProj !arena !recNf (FieldId !fid) =
  internPackedNode arena NT_Proj fid recNf (-1) (-1)

-- | Intern a stuck neutral record merge node (@//@ or @/\\@).
{-# INLINE internNfMerge #-}
internNfMerge :: NfArena s -> RecordOp -> Int32 -> Int32 -> ST s Int32
internNfMerge !arena !op !lhsNf !rhsNf =
  let !tag = case op of
        OpPreferR     -> NT_PreferR
        OpCombineDeep -> NT_CombineDeep
        OpRestrict    -> NT_PreferR
  in internPackedNode arena tag 0 lhsNf rhsNf (-1)

-- | Intern a normalized record with 'SchemaId' and a flat 'SmallArray' of field 'NfAddr's.
--   Folds the field array through hash-consed 'NT_RecordCons' pairs so records of
--   arbitrary width share common field prefixes in 'SwissTable128'.
internNfRecord :: NfArena s -> SchemaId -> SmallArray Int32 -> ST s Int32
internNfRecord !arena (SchemaId !sid) !fieldNfs = do
  !nilNf <- internPackedNode arena NT_RecordNil 0 (-1) (-1) (-1)
  let !n = sizeofSmallArray fieldNfs
      foldFields !i !accNf
        | i >= n    = internPackedNode arena NT_RecordRoot sid accNf (-1) (-1)
        | otherwise = do
            let !fNf = indexSmallArray fieldNfs i
            !nextAcc <- internPackedNode arena NT_RecordCons (fromIntegral i) accNf fNf (-1)
            foldFields (i + 1) nextAcc
  foldFields 0 nilNf

-- | Decide judgmental (@alpha-beta@) equality of two normalized expressions in O(1) time.
{-# INLINE judgmentallyEqualNf #-}
judgmentallyEqualNf :: Int32 -> Int32 -> Bool
judgmentallyEqualNf !nfA !nfB = nfA == nfB
