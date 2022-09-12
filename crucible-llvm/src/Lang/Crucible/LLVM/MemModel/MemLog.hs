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
{-# Language ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.MemLog
  (
    -- * Allocation logs
    AllocType(..)
  , Mutability(..)
  , AllocInfo(..)
  , MemAllocs(..)
  , MemAlloc(..)
  , sizeMemAllocs
  , allocMemAllocs
  , freeMemAllocs
  , muxMemAllocs
  , popMemAllocs
  , possibleAllocInfo
  , isAllocatedGeneric
    -- * Write logs
  , WriteSource(..)
  , MemWrite(..)
  , MemWrites(..)
  , MemWritesChunk(..)
  , memWritesSingleton
    -- * Memory logs
  , MemState(..)
  , MemChanges
  , memState
  , Mem(..)
  , emptyChanges
  , emptyMem
  , memEndian

    -- * Pretty printing
  , ppType
  , ppPtr
  , ppAllocInfo
  , ppAllocs
  , ppMem
  , ppMemWrites
  , ppWrite

    -- * Write ranges
  , writeRangesMem

    -- * Concretization
  , concPtr
  , concLLVMVal
  , concMem
  ) where

import           Control.Applicative ((<|>))
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Foldable
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List.Extra as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe)
import           Data.Text (Text)
import           Numeric.Natural
import           Prettyprinter

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Ctx (SingleCtx)

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment, EndianForm(..))
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Value
import qualified Text.Printf as Text

--------------------------------------------------------------------------------
-- Allocations

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Eq, Ord, Show)

data Mutability = Mutable | Immutable
  deriving (Eq, Ord, Show)

-- | Details of a single allocation. The @Maybe SymBV@ argument is either a
-- size or @Nothing@ representing an unbounded allocation. The 'Mutability'
-- indicates whether the region is read-only. The 'String' contains source
-- location information for use in error messages.
data AllocInfo sym =
  forall w. (1 <= w) => AllocInfo AllocType (Maybe (SymBV sym w)) Mutability Alignment String

-- | Stores writeable memory allocations.
data MemAlloc sym
    -- | A collection of consecutive basic allocations.
  = Allocations (Map Natural (AllocInfo sym))
    -- | Freeing of the given block ID.
  | MemFree (SymNat sym) String
    -- | The merger of two allocations.
  | AllocMerge (Pred sym) (MemAllocs sym) (MemAllocs sym)

-- | A record of which memory regions have been allocated or freed.

-- Memory allocations are represented as a list with the invariant
-- that any two adjacent 'Allocations' constructors must be merged
-- together, and that no 'Allocations' constructor has an empty map.
newtype MemAllocs sym = MemAllocs [MemAlloc sym]

instance Semigroup (MemAllocs sym) where
  (MemAllocs lhs_allocs) <> (MemAllocs rhs_allocs)
    | Just (lhs_head_allocs, Allocations lhs_m) <- List.unsnoc lhs_allocs
    , Allocations rhs_m : rhs_tail_allocs <- rhs_allocs
    = MemAllocs (lhs_head_allocs ++ [Allocations (Map.union lhs_m rhs_m)] ++ rhs_tail_allocs)
    | otherwise = MemAllocs (lhs_allocs ++ rhs_allocs)

instance Monoid (MemAllocs sym) where
  mempty = MemAllocs []


sizeMemAlloc :: MemAlloc sym -> Int
sizeMemAlloc =
  \case
    Allocations m -> Map.size m
    MemFree{} -> 1
    AllocMerge{} -> 1

-- | Compute the size of a 'MemAllocs' log.
sizeMemAllocs :: MemAllocs sym -> Int
sizeMemAllocs (MemAllocs allocs) = sum (map sizeMemAlloc allocs)

-- | Returns true if this consists of a empty collection of memory allocs.
nullMemAllocs :: MemAllocs sym -> Bool
nullMemAllocs (MemAllocs xs) = null xs

-- | Allocate a new block with the given allocation ID.
allocMemAllocs :: Natural -> AllocInfo sym -> MemAllocs sym -> MemAllocs sym
allocMemAllocs blk info ma = MemAllocs [Allocations (Map.singleton blk info)] <> ma

-- | Free the block with the given allocation ID.
freeMemAllocs :: SymNat sym -> String {- ^ Location info for debugging -} -> MemAllocs sym -> MemAllocs sym
freeMemAllocs blk loc (MemAllocs xs) = MemAllocs (MemFree blk loc : xs)

muxMemAllocs :: IsExpr (SymExpr sym) => Pred sym -> MemAllocs sym -> MemAllocs sym -> MemAllocs sym
muxMemAllocs _ (MemAllocs []) (MemAllocs []) = MemAllocs []
muxMemAllocs c xs ys =
  case asConstantPred c of
    Just True -> xs
    Just False -> ys
    Nothing -> MemAllocs [AllocMerge c xs ys]

-- | Purge all stack allocations from the allocation log.
popMemAllocs :: forall sym. MemAllocs sym -> MemAllocs sym
popMemAllocs (MemAllocs xs) = MemAllocs (mapMaybe popMemAlloc xs)
  where
    popMemAlloc :: MemAlloc sym -> Maybe (MemAlloc sym)
    popMemAlloc (Allocations am) =
      if Map.null am' then Nothing else Just (Allocations am')
      where am' = Map.filter notStackAlloc am
    popMemAlloc a@(MemFree _ _) = Just a
    popMemAlloc (AllocMerge c x y) = Just (AllocMerge c (popMemAllocs x) (popMemAllocs y))

    notStackAlloc :: AllocInfo sym -> Bool
    notStackAlloc (AllocInfo x _ _ _ _) = x /= StackAlloc

-- | Look up the 'AllocInfo' for the given allocation number. A 'Just'
-- result indicates that the specified memory region may or may not
-- still be allocated; 'Nothing' indicates that the memory region is
-- definitely not allocated.
possibleAllocInfo ::
  forall sym.
  IsExpr (SymExpr sym) =>
  Natural ->
  MemAllocs sym ->
  Maybe (AllocInfo sym)
possibleAllocInfo n (MemAllocs xs) = asum (map helper xs)
  where
    helper :: MemAlloc sym -> Maybe (AllocInfo sym)
    helper =
      \case
        MemFree _ _ -> Nothing
        Allocations m -> Map.lookup n m
        AllocMerge cond ma1 ma2 ->
          case asConstantPred cond of
            Just True -> possibleAllocInfo n ma1
            Just False -> possibleAllocInfo n ma2
            Nothing -> possibleAllocInfo n ma1 <|> possibleAllocInfo n ma2


-- | Generalized function for checking whether a memory region ID is allocated.
--
-- The first predicate indicates whether the region was allocated, the second
-- indicates whether it has *not* been freed.
isAllocatedGeneric ::
  forall sym.
  (IsExpr (SymExpr sym), IsExprBuilder sym) =>
  sym ->
  (AllocInfo sym -> IO (Pred sym)) ->
  SymNat sym ->
  MemAllocs sym ->
  IO (Pred sym, Pred sym)
isAllocatedGeneric sym inAlloc blk = go (pure (falsePred sym)) (pure (truePred sym))
  where
    go :: IO (Pred sym) -> IO (Pred sym) -> MemAllocs sym -> IO (Pred sym, Pred sym)
    go fallback fallbackFreed (MemAllocs []) = (,) <$> fallback <*> fallbackFreed
    go fallback fallbackFreed (MemAllocs (alloc : r)) =
      case alloc of
        Allocations am ->
          case asNat blk of
            Just b -> -- concrete block number, look up entry
              case Map.lookup b am of
                Nothing -> go fallback fallbackFreed (MemAllocs r)
                Just ba -> (,) <$> inAlloc ba <*> fallbackFreed
            Nothing -> -- symbolic block number, need to check all entries
              Map.foldrWithKey checkEntry (go fallback fallbackFreed (MemAllocs r)) am
              where
                checkEntry a ba k =
                  do
                     sameBlock <- natEq sym blk =<< natLit sym a
                     case asConstantPred sameBlock of
                       Just True ->
                         -- This is where where this block was allocated, and it
                         -- couldn't have been freed before it was allocated.
                         --
                         -- NOTE(lb): It's not clear to me that this branch is
                         -- reachable: If the equality test can succeed
                         -- concretely, wouldn't asNat have returned a Just
                         -- above? In either case, this answer should be sound.
                         return (truePred sym, truePred sym)
                       Just False -> k
                       Nothing ->
                         do (fallback', fallbackFreed') <- k
                            here <- itePredM sym sameBlock (inAlloc ba) (pure fallback')
                            pure (here, fallbackFreed')
        MemFree a _ ->
          do sameBlock <- natEq sym blk a
             case asConstantPred sameBlock of
               Just True  ->
                 -- If it was freed, it also must have been allocated beforehand.
                 return (truePred sym, falsePred sym)
               Just False -> go fallback fallbackFreed (MemAllocs r)
               Nothing    ->
                 do (inRest, notFreedInRest) <-
                      go fallback fallbackFreed (MemAllocs r)
                    notSameBlock <- notPred sym sameBlock
                    (inRest,) <$> andPred sym notSameBlock notFreedInRest
        AllocMerge _ (MemAllocs []) (MemAllocs []) ->
          go fallback fallbackFreed (MemAllocs r)
        AllocMerge c xr yr ->
          do (inRest, notFreedInRest) <- go fallback fallbackFreed (MemAllocs r) -- TODO: wrap this in a delay
             (inTrue, notFreedInTrue) <- go (pure inRest) (pure notFreedInRest) xr
             (inFalse, notFreedInFalse) <- go (pure inRest) (pure notFreedInRest) yr
             (,) <$> itePred sym c inTrue inFalse
                 <*> itePred sym c notFreedInTrue notFreedInFalse

--------------------------------------------------------------------------------
-- Writes

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


--------------------------------------------------------------------------------
-- Memory

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
    -- The text value gives a user-consumable name for the stack frame.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | StackFrame !Int !Int Text (MemChanges sym) (MemState sym)
    -- | Represents a push of a branch frame, and changes since that branch.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | BranchFrame !Int !Int (MemChanges sym) (MemState sym)

type MemChanges sym = (MemAllocs sym, MemWrites sym)

-- | Memory writes are represented as a list of chunks of writes.
--   Chunks alternate between being indexed and being flat.
newtype MemWrites sym = MemWrites [MemWritesChunk sym]

-- | Returns true if this consists of a empty collection of memory writes
nullMemWrites :: MemWrites sym -> Bool
nullMemWrites (MemWrites ws) = null ws

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
emptyChanges = (mempty, mempty)

emptyMem :: EndianForm -> Mem sym
emptyMem e = Mem { memEndianForm = e, _memState = EmptyMem 0 0 emptyChanges }

memEndian :: Mem sym -> EndianForm
memEndian = memEndianForm


--------------------------------------------------------------------------------
-- Pretty printing

ppMerge :: IsExpr e
        => (v -> Doc ann)
        -> e tp
        -> [v]
        -> [v]
        -> Doc ann
ppMerge vpp c x y =
  indent 2 $
  vcat
  [ "Condition:"
  , indent 2 (printSymExpr c)
  , ppAllocList x "True Branch:"
  , ppAllocList y "False Branch:"
  ]
  where ppAllocList [] d = d <+> "<none>"
        ppAllocList xs d = vcat [d, indent 2 (vcat $ map vpp xs)]

ppAlignment :: Alignment -> Doc ann
ppAlignment a =
  pretty $ show (fromAlignment a) ++ "-byte-aligned"

ppAllocInfo :: IsExpr (SymExpr sym) => (Natural, AllocInfo sym) -> Doc ann
ppAllocInfo (base, AllocInfo atp sz mut alignment loc) =
  viaShow atp
  <+> pretty base
  <+> maybe mempty printSymExpr sz
  <+> viaShow mut
  <+> ppAlignment alignment
  <+> pretty loc

ppAlloc :: IsExpr (SymExpr sym) => MemAlloc sym -> Doc ann
ppAlloc (Allocations xs) =
  vcat $ map ppAllocInfo (reverse (Map.assocs xs))
ppAlloc (MemFree base loc) =
  "Free" <+> printSymNat base <+> pretty loc
ppAlloc (AllocMerge c (MemAllocs x) (MemAllocs y)) =
  vcat ["Merge", ppMerge ppAlloc c x y]

ppAllocs :: IsExpr (SymExpr sym) => MemAllocs sym -> Doc ann
ppAllocs (MemAllocs xs) = vcat $ map ppAlloc xs

ppWrite :: IsExpr (SymExpr sym) => MemWrite sym -> Doc ann
ppWrite (MemWrite d (MemCopy s l)) = do
  "memcopy" <+> ppPtr d <+> ppPtr s <+> printSymExpr l
ppWrite (MemWrite d (MemSet v l)) = do
  "memset" <+> ppPtr d <+> printSymExpr v <+> printSymExpr l
ppWrite (MemWrite d (MemStore v _ _)) = do
  pretty '*' <> ppPtr d <+> ":=" <+> ppTermExpr v
ppWrite (MemWrite d (MemArrayStore arr _)) = do
  pretty '*' <> ppPtr d <+> ":=" <+> printSymExpr arr
ppWrite (MemWrite d (MemInvalidate msg l)) = do
  "invalidate" <+> parens (pretty msg) <+> ppPtr d <+> printSymExpr l
ppWrite (WriteMerge c (MemWrites x) (MemWrites y)) = do
  vcat ["merge", ppMerge ppMemWritesChunk c x y]

ppMemWritesChunk :: IsExpr (SymExpr sym) => MemWritesChunk sym -> Doc ann
ppMemWritesChunk = \case
  MemWritesChunkFlat [] ->
    "No writes"
  MemWritesChunkFlat flat_writes ->
    vcat $ map ppWrite flat_writes
  MemWritesChunkIndexed indexed_writes ->
    vcat
    [ "Indexed chunk:"
    , indent 2 (vcat $ map
        (\(blk, blk_writes) ->
          case blk_writes of
            [] -> mempty
            _  -> viaShow blk <+> "|->" <> softline <>
                    indent 2 (vcat $ map ppWrite blk_writes))
        (IntMap.toList indexed_writes))
    ]

ppMemWrites :: IsExpr (SymExpr sym) => MemWrites sym -> Doc ann
ppMemWrites (MemWrites ws) = vcat $ map ppMemWritesChunk ws

ppMemChanges :: IsExpr (SymExpr sym) => MemChanges sym -> [Doc ann]
ppMemChanges (al,wl)
  | nullMemAllocs al && nullMemWrites wl = ["No writes or allocations"]
  | otherwise =
      (if nullMemAllocs al then [] else ["Allocations:", indent 2 (ppAllocs al)]) <>
      (if nullMemWrites wl then [] else ["Writes:", indent 2 (ppMemWrites wl)])

ppMemState :: (MemChanges sym -> [Doc ann]) -> MemState sym -> Doc ann
ppMemState f (EmptyMem _ _ d) =
  vcat ("Base memory" : map (indent 2) (f d))
ppMemState f (StackFrame _ _ nm d ms) =
  vcat (("Stack frame" <+> pretty nm) : map (indent 2) (f d) ++ [ppMemState f ms])
ppMemState f (BranchFrame _ _ d ms) =
  vcat ("Branch frame" : map (indent 2) (f d) ++ [ppMemState f ms])

ppMem :: IsExpr (SymExpr sym) => Mem sym -> Doc ann
ppMem m = ppMemState ppMemChanges (m^.memState)


------------------------------------------------------------------------------
-- Write ranges

multiUnion :: (Ord k, Semigroup a) => Map k a -> Map k a -> Map k a
multiUnion = Map.unionWith (<>)

writeSourceSize ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  WriteSource sym w ->
  MaybeT IO (SymBV sym w)
writeSourceSize sym = \case
  MemCopy _src sz -> pure sz
  MemSet _val sz -> pure sz
  MemStore _val st _align ->
    liftIO $ bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth $ toInteger $ typeEnd 0 st
  MemArrayStore _arr Nothing -> MaybeT $ pure Nothing
  MemArrayStore _arr (Just sz) -> pure sz
  MemInvalidate _nm sz -> pure sz

writeRangesMemWrite ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  MemWrite sym ->
  MaybeT IO (Map Natural [(SymBV sym w, SymBV sym w)])
writeRangesMemWrite sym = \case
  MemWrite ptr wsrc
    | Just Refl <- testEquality ?ptrWidth (ptrWidth ptr) ->
      case asNat (llvmPointerBlock ptr) of
        Just blk -> do
          sz <- writeSourceSize sym wsrc
          pure $ Map.singleton blk [(llvmPointerOffset ptr, sz)]
        Nothing -> MaybeT $ pure Nothing
    | otherwise -> fail "foo"
  WriteMerge _p ws1 ws2 ->
    multiUnion <$> writeRangesMemWrites sym ws1 <*> writeRangesMemWrites sym ws2

writeRangesMemWritesChunk ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  MemWritesChunk sym ->
  MaybeT IO (Map Natural [(SymBV sym w, SymBV sym w)])
writeRangesMemWritesChunk sym = \case
  MemWritesChunkFlat ws -> foldl multiUnion Map.empty <$> mapM (writeRangesMemWrite sym) ws
  MemWritesChunkIndexed mp ->
    foldl multiUnion Map.empty <$> mapM (writeRangesMemWrite sym) (concat $ IntMap.elems mp)

writeRangesMemWrites ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  MemWrites sym ->
  MaybeT IO (Map Natural [(SymBV sym w, SymBV sym w)])
writeRangesMemWrites sym (MemWrites ws) =
  foldl multiUnion Map.empty <$> mapM (writeRangesMemWritesChunk sym) ws

writeRangesMemChanges ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  MemChanges sym ->
  MaybeT IO (Map Natural [(SymBV sym w, SymBV sym w)])
writeRangesMemChanges sym (_as, ws) = writeRangesMemWrites sym ws

writeRangesMemState ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  MemState sym ->
  MaybeT IO (Map Natural [(SymBV sym w, SymBV sym w)])
writeRangesMemState sym = \case
  EmptyMem _a _w chs -> writeRangesMemChanges sym chs
  StackFrame _a _w _nm chs st ->
    multiUnion <$> writeRangesMemChanges sym chs <*> writeRangesMemState sym st
  BranchFrame _a _w chs st ->
    multiUnion <$> writeRangesMemChanges sym chs <*> writeRangesMemState sym st

-- | Compute the ranges (pairs of the form pointer offset and size) for all
-- memory writes, indexed by the pointer base. The result is Nothing if the
-- memory contains any writes with symbolic pointer base, or without size.
writeRangesMem ::
  (IsExprBuilder sym, HasPtrWidth w) =>
  sym ->
  Mem sym ->
  MaybeT IO ((Map Natural [(SymBV sym w, SymBV sym w)]))
writeRangesMem sym mem = writeRangesMemState sym $ mem ^. memState


------------------------------------------------------------------------------
-- Concretization

concAllocInfo ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  AllocInfo sym -> IO (AllocInfo sym)
concAllocInfo sym conc (AllocInfo atp sz m a nm) =
  do sz' <- traverse (concBV sym conc) sz
     pure (AllocInfo atp sz' m a nm)

concAlloc ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemAlloc sym -> IO (MemAllocs sym)
concAlloc sym conc (Allocations m) =
  do m' <- traverse (concAllocInfo sym conc) m
     pure (MemAllocs [Allocations m'])
concAlloc sym conc (MemFree blk loc) =
  do blk' <- integerToNat sym =<< intLit sym =<< conc =<< natToInteger sym blk
     pure (MemAllocs [MemFree blk' loc])
concAlloc sym conc (AllocMerge p m1 m2) =
  do b <- conc p
     if b then concMemAllocs sym conc m1
          else concMemAllocs sym conc m2

concMemAllocs ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemAllocs sym -> IO (MemAllocs sym)
concMemAllocs sym conc (MemAllocs cs) =
  fold <$> traverse (concAlloc sym conc) cs

concLLVMVal ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  LLVMVal sym -> IO (LLVMVal sym)
concLLVMVal sym conc (LLVMValInt blk off) =
  do blk' <- integerToNat sym =<< intLit sym =<< conc =<< natToInteger sym blk
     off' <- concBV sym conc off
     pure (LLVMValInt blk' off')
concLLVMVal _sym _conc (LLVMValFloat fs fi) =
  pure (LLVMValFloat fs fi) -- TODO concreteize floats
concLLVMVal sym conc (LLVMValStruct fs) =
  LLVMValStruct <$> traverse (\ (fi,v) -> (,) <$> pure fi <*> concLLVMVal sym conc v) fs
concLLVMVal sym conc (LLVMValArray st vs) =
  LLVMValArray st <$> traverse (concLLVMVal sym conc) vs
concLLVMVal _ _ v@LLVMValString{} = pure v
concLLVMVal _ _ v@LLVMValZero{} = pure v
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
  (,) <$> concMemAllocs sym conc as <*> concMemWrites sym conc ws


concMemState ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemState sym -> IO (MemState sym)
concMemState sym conc (EmptyMem a w chs) =
  EmptyMem a w <$> concMemChanges sym conc chs
concMemState sym conc (StackFrame a w nm frm stk) =
  StackFrame a w nm <$> concMemChanges sym conc frm <*> concMemState sym conc stk
concMemState sym conc (BranchFrame a w frm stk) =
  BranchFrame a w <$> concMemChanges sym conc frm <*> concMemState sym conc stk

concMem ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  Mem sym -> IO (Mem sym)
concMem sym conc (Mem endian st) =
  Mem endian <$> concMemState sym conc st
