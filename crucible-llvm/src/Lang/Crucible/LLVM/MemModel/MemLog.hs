------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.MemLog
-- Description      : Data types supporting the LLVM memory model
-- Copyright        : (c) Galois, Inc 2011-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.MemLog
  ( AllocType(..)
  , Mutability(..)
  , MemAlloc(..)
  , WriteSource(..)
  , MemWrite(..)
  , MemState(..)
  , MemWrites(..)
  , MemWritesChunk(..)
  , MemChanges
  , memState
  , Mem(..)
  , emptyChanges
  , emptyMem
  , memEndian
  , memWritesSingleton

    -- * Pretty printing
  , ppType
  , ppPtr
  , ppAlloc
  , ppAllocs
  , ppMem
  , ppWrite

    -- * Concretization
  , concBV
  , concPtr
  , concLLVMVal
  , concMem
  ) where

import           Control.Lens
import           Data.Foldable
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List.Extra as List
import           Data.Text (Text, unpack)
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Ctx (SingleCtx)

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment, EndianForm(..))
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Value

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Eq, Ord, Show)

data Mutability = Mutable | Immutable
  deriving (Eq, Ord, Show)

-- | Stores writeable memory allocations.
data MemAlloc sym
     -- | Allocation with given block ID. The @Maybe SymBV@ argument is either a
     -- size or @Nothing@ representing an unbounded allocation. The 'Mutability'
     -- indicates whether the region is read-only. The 'String' contains source
     -- location information for use in error messages.
   = forall w. (1 <= w) => Alloc AllocType Natural (Maybe (SymBV sym w)) Mutability Alignment String
     -- | Freeing of the given block ID.
   | MemFree (SymNat sym)
     -- | The merger of two allocations.
   | AllocMerge (Pred sym) [MemAlloc sym] [MemAlloc sym]

data WriteSource sym w
    -- | @MemCopy src len@ copies @len@ bytes from [src..src+len).
  = MemCopy (LLVMPtr sym w) (SymBV sym w)
    -- | @MemSet val len@ fills the destination with @len@ copies of byte @val@.
  | MemSet (SymBV sym 8) (SymBV sym w)
    -- | @MemStore val ty al@ writes value @val@ with type @ty@ at the destination.
    --   with alignment at least @al@.
  | MemStore (LLVMVal sym) StorageType Alignment
    -- | @MemArrayStore block (Just len)@ writes byte-array @block@ of size
    -- @len@ at the destination; @MemArrayStore block Nothing@ writes byte-array
    -- @block@ of unbounded size
  | MemArrayStore (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)) (Maybe (SymBV sym w))
    -- | @MemInvalidate len@ flags @len@ bytes as uninitialized.
  | MemInvalidate Text (SymBV sym w)

data MemWrite sym
    -- | @MemWrite dst src@ represents a write to @dst@ from the given source.
  = forall w. (1 <= w) => MemWrite (LLVMPtr sym w) (WriteSource sym w)
    -- | The merger of two memories.
  | WriteMerge (Pred sym) (MemWrites sym) (MemWrites sym)


-- | A symbolic representation of the LLVM heap.
--
-- This representation is designed to support a variety of operations
-- including reads and writes of symbolic data to symbolic addresses,
-- symbolic memcpy and memset, and merging two memories in a single
-- memory using an if-then-else operation.
--
-- A common use case is that the symbolic simulator will branch into
-- two execution states based on a symbolic branch, make different
-- memory modifications on each branch, and then need to merge the two
-- memories to resume execution along a single path using the branch
-- condition.  To support this, our memory representation supports
-- "branch frames", at any point one can insert a fresh branch frame
-- (see `branchMem`), and then at some later point merge two memories
-- back into a single memory (see `mergeMem`).  Our `mergeMem`
-- implementation is able to efficiently merge memories, but requires
-- that one only merge memories that were identical prior to the last
-- branch.
data Mem sym = Mem { memEndianForm :: EndianForm, _memState :: MemState sym }

memState :: Lens' (Mem sym) (MemState sym)
memState = lens _memState (\s v -> s { _memState = v })

-- | A state of memory as of a stack push, branch, or merge.  Counts
-- of the total number of allocations and writes are kept for
-- performance metrics.
data MemState sym =
    -- | Represents initial memory and changes since then.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
    EmptyMem !Int !Int (MemChanges sym)
    -- | Represents a push of a stack frame, and changes since that stack push.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | StackFrame !Int !Int (MemChanges sym) (MemState sym)
    -- | Represents a push of a branch frame, and changes since that branch.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | BranchFrame !Int !Int (MemChanges sym) (MemState sym)

type MemChanges sym = ([MemAlloc sym], MemWrites sym)

-- | Memory writes are represented as a list of chunks of writes.
--   Chunks alternate between being indexed and being flat.
newtype MemWrites sym = MemWrites [MemWritesChunk sym]

-- | A chunk of memory writes is either indexed or flat (unindexed).
--   An indexed chunk consists of writes to addresses with concrete
--   base pointers and is represented as a map. A flat chunk consists of
--   writes to addresses with symbolic base pointers. A merge of two
--   indexed chunks is a indexed chunk, while any other merge is part of
--   a flat chunk.
data MemWritesChunk sym =
    MemWritesChunkFlat [MemWrite sym]
  | MemWritesChunkIndexed (IntMap [MemWrite sym])

instance Semigroup (MemWrites sym) where
  (MemWrites lhs_writes) <> (MemWrites rhs_writes)
    | Just (lhs_head_writes, lhs_tail_write) <- List.unsnoc lhs_writes
    , MemWritesChunkIndexed lhs_tail_indexed_writes <- lhs_tail_write
    , rhs_head_write : rhs_tail_writes <- rhs_writes
    , (MemWritesChunkIndexed rhs_head_indexed_writes) <- rhs_head_write = do
      let merged_chunk = MemWritesChunkIndexed $ IntMap.mergeWithKey
            (\_ lhs_alloc_writes rhs_alloc_writes ->
              Just $ lhs_alloc_writes ++ rhs_alloc_writes)
            id
            id
            lhs_tail_indexed_writes
            rhs_head_indexed_writes
      MemWrites $ lhs_head_writes ++ [merged_chunk] ++ rhs_tail_writes
    | otherwise = MemWrites $ lhs_writes ++ rhs_writes

instance Monoid (MemWrites sym) where
  mempty = MemWrites []


memWritesSingleton ::
  (IsExprBuilder sym, 1 <= w) =>
  LLVMPtr sym w ->
  WriteSource sym w ->
  MemWrites sym
memWritesSingleton ptr src
  | Just blk <- asNat (llvmPointerBlock ptr)
  , isIndexableSource src =
    MemWrites
      [ MemWritesChunkIndexed $
          IntMap.singleton (fromIntegral blk) [MemWrite ptr src]
      ]
  | otherwise = MemWrites [MemWritesChunkFlat [MemWrite ptr src]]
  where
    isIndexableSource ::  WriteSource sym w -> Bool
    isIndexableSource = \case
      MemStore{} -> True
      MemArrayStore{} -> True
      MemSet{} -> True
      MemInvalidate{} -> True
      MemCopy{} -> False



emptyChanges :: MemChanges sym
emptyChanges = ([], mempty)

emptyMem :: EndianForm -> Mem sym
emptyMem e = Mem { memEndianForm = e, _memState = EmptyMem 0 0 emptyChanges }

memEndian :: Mem sym -> EndianForm
memEndian = memEndianForm


--------------------------------------------------------------------------------
-- Pretty printing

ppMerge :: IsExpr e
        => (v -> Doc)
        -> e tp
        -> [v]
        -> [v]
        -> Doc
ppMerge vpp c x y =
  indent 2 $
    text "Condition:" <$$>
    indent 2 (printSymExpr c) <$$>
    ppAllocList x (text "True Branch:") <$$>
    ppAllocList y (text "False Branch:")
  where ppAllocList [] = (<+> text "<none>")
        ppAllocList xs = (<$$> indent 2 (vcat $ map vpp xs))

ppAlignment :: Alignment -> Doc
ppAlignment a =
  text $ show (fromAlignment a) ++ "-byte-aligned"

ppAlloc :: IsExpr (SymExpr sym) => MemAlloc sym -> Doc
ppAlloc (Alloc atp base sz mut alignment loc) =
  text (show atp)
  <+> text (show base)
  <+> (pretty $ printSymExpr <$> sz)
  <+> text (show mut)
  <+> ppAlignment alignment
  <+> text loc
ppAlloc (MemFree base) =
  text "Free" <+> printSymExpr base
ppAlloc (AllocMerge c x y) = do
  text "Merge" <$$> ppMerge ppAlloc c x y

ppAllocs :: IsExpr (SymExpr sym) => [MemAlloc sym] -> Doc
ppAllocs xs = vcat $ map ppAlloc xs

ppWrite :: IsExpr (SymExpr sym) => MemWrite sym -> Doc
ppWrite (MemWrite d (MemCopy s l)) = do
  text "memcopy" <+> ppPtr d <+> ppPtr s <+> printSymExpr l
ppWrite (MemWrite d (MemSet v l)) = do
  text "memset" <+> ppPtr d <+> printSymExpr v <+> printSymExpr l
ppWrite (MemWrite d (MemStore v _ _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> ppTermExpr v
ppWrite (MemWrite d (MemArrayStore arr _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> printSymExpr arr
ppWrite (MemWrite d (MemInvalidate msg l)) = do
  text "invalidate" <+> parens (text $ unpack msg) <+> ppPtr d <+> printSymExpr l
ppWrite (WriteMerge c (MemWrites x) (MemWrites y)) = do
  text "merge" <$$> ppMerge ppMemWritesChunk c x y

ppMemWritesChunk :: IsExpr (SymExpr sym) => MemWritesChunk sym -> Doc
ppMemWritesChunk = \case
  MemWritesChunkIndexed indexed_writes ->
    text "Indexed chunk:" <$$>
    indent 2 (vcat $ map
      (\(blk, blk_writes) ->
        text (show blk) <+> "|->" <$$>
        indent 2 (vcat $ map ppWrite blk_writes))
      (IntMap.toList indexed_writes))
  MemWritesChunkFlat flat_writes ->
    text "Flat chunk:" <$$>
    indent 2 (vcat $ map ppWrite flat_writes)

ppMemWrites :: IsExpr (SymExpr sym) => MemWrites sym -> Doc
ppMemWrites (MemWrites ws) = vcat $ map ppMemWritesChunk ws

ppMemChanges :: IsExpr (SymExpr sym) => MemChanges sym -> Doc
ppMemChanges (al,wl) =
  text "Allocations:" <$$>
  indent 2 (ppAllocs al) <$$>
  text "Writes:" <$$>
  indent 2 (ppMemWrites wl)

ppMemState :: (MemChanges sym -> Doc) -> MemState sym -> Doc
ppMemState f (EmptyMem _ _ d) = do
  text "Base memory" <$$> indent 2 (f d)
ppMemState f (StackFrame _ _ d ms) = do
  text "Stack frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms
ppMemState f (BranchFrame _ _ d ms) = do
  text "Branch frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms

ppMem :: IsExpr (SymExpr sym) => Mem sym -> Doc
ppMem m = ppMemState ppMemChanges (m^.memState)


------------------------------------------------------------------------------
-- Concretization


concBV ::
  (IsExprBuilder sym, 1 <= w) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  SymBV sym w -> IO (SymBV sym w)
concBV sym conc bv =
  do bv' <- conc bv
     bvLit sym (bvWidth bv) bv'

concPtr ::
  (IsExprBuilder sym, 1 <= wptr) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  LLVMPtr sym wptr -> IO (LLVMPtr sym wptr)
concPtr sym conc (LLVMPointer blk off) =
  LLVMPointer <$>
     (natLit sym =<< conc blk) <*>
     (concBV sym conc off)

concAlloc ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemAlloc sym -> IO [MemAlloc sym]
concAlloc sym conc (Alloc atp blk sz m a nm) =
  do sz' <- traverse (concBV sym conc) sz
     pure [Alloc atp blk sz' m a nm]
concAlloc sym conc (MemFree blk) =
  do blk' <- natLit sym =<< conc blk
     pure [MemFree blk']
concAlloc sym conc (AllocMerge p m1 m2) =
  do b <- conc p
     if b then (concat <$> mapM (concAlloc sym conc) m1)
          else (concat <$> mapM (concAlloc sym conc) m2)

concLLVMVal ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  LLVMVal sym -> IO (LLVMVal sym)
concLLVMVal sym conc (LLVMValInt blk off) =
  LLVMValInt <$> (natLit sym =<< conc blk) <*> (concBV sym conc off)
concLLVMVal _sym _conc (LLVMValFloat fs fi) =
  pure (LLVMValFloat fs fi) -- TODO concreteize floats
concLLVMVal sym conc (LLVMValStruct fs) =
  LLVMValStruct <$> traverse (\ (fi,v) -> (,) <$> pure fi <*> concLLVMVal sym conc v) fs
concLLVMVal sym conc (LLVMValArray st vs) =
  LLVMValArray st <$> traverse (concLLVMVal sym conc) vs
concLLVMVal _ _ (LLVMValZero st) =
  pure (LLVMValZero st)
concLLVMVal _ _ (LLVMValUndef st) =
  pure (LLVMValZero st) -- ??? does it make sense to turn Undef into Zero?


concWriteSource ::
  (IsExprBuilder sym, 1 <= w) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  WriteSource sym w -> IO (WriteSource sym w)
concWriteSource sym conc (MemCopy src len) =
  MemCopy <$> (concPtr sym conc src) <*> (concBV sym conc len)
concWriteSource sym conc (MemSet val len) =
  MemSet <$> (concBV sym conc val) <*> (concBV sym conc len)
concWriteSource sym conc (MemStore val st a) =
  MemStore <$> concLLVMVal sym conc val <*> pure st <*> pure a

concWriteSource _sym _conc (MemArrayStore arr Nothing) =
  -- TODO, concretize the actual array
  pure (MemArrayStore arr Nothing)
concWriteSource sym conc (MemArrayStore arr (Just sz)) =
  -- TODO, concretize the actual array
  MemArrayStore arr . Just <$> concBV sym conc sz

concWriteSource sym conc (MemInvalidate nm len) =
  MemInvalidate nm <$> concBV sym conc len

concMemWrite ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemWrite sym -> IO (MemWrites sym)
concMemWrite sym conc (MemWrite ptr wsrc) =
  do ptr' <- concPtr sym conc ptr
     wsrc' <- concWriteSource sym conc wsrc
     pure $ memWritesSingleton ptr' wsrc'
concMemWrite sym conc (WriteMerge p m1 m2) =
  do b <- conc p
     if b then concMemWrites sym conc m1
          else concMemWrites sym conc m2

concMemWrites ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemWrites sym -> IO (MemWrites sym)
concMemWrites sym conc (MemWrites cs) =
  fold <$> mapM (concMemWritesChunk sym conc) cs

concMemWritesChunk ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemWritesChunk sym -> IO (MemWrites sym)
concMemWritesChunk sym conc (MemWritesChunkFlat ws) =
  fold <$> mapM (concMemWrite sym conc) ws
concMemWritesChunk sym conc (MemWritesChunkIndexed mp) =
  fold <$> mapM (concMemWrite sym conc) (concat (IntMap.elems mp))

concMemChanges ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemChanges sym -> IO (MemChanges sym)
concMemChanges sym conc (as, ws) =
  (,) <$> (concat <$> mapM (concAlloc sym conc) as) <*> concMemWrites sym conc ws


concMemState ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemState sym -> IO (MemState sym)
concMemState sym conc (EmptyMem a w chs) =
  EmptyMem a w <$> concMemChanges sym conc chs
concMemState sym conc (StackFrame a w frm stk) =
  StackFrame a w <$> concMemChanges sym conc frm <*> concMemState sym conc stk
concMemState sym conc (BranchFrame a w frm stk) =
  BranchFrame a w <$> concMemChanges sym conc frm <*> concMemState sym conc stk

concMem ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  Mem sym -> IO (Mem sym)
concMem sym conc (Mem endian st) =
  Mem endian <$> concMemState sym conc st
