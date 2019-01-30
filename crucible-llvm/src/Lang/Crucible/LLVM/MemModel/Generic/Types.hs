{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.MemModel.Generic.Types
  () where

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Show)

data Mutability = Mutable | Immutable
  deriving (Eq, Show)

-- | Stores writeable memory allocations.
data MemAlloc sym
     -- | Allocation with given block ID and number of bytes. The
     -- 'Mutability' indicates whether the region is read-only. The
     -- 'String' contains source location information for use in error
     -- messages.
   = forall w. Alloc AllocType Natural (SymBV sym w) Mutability Alignment String
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
    -- | @MemStoreBlock block len@ writes byte-array @block@ of size @len@
    -- at the destination.
  | MemArrayStore (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)) (SymBV sym w)

data MemWrite sym
    -- | @MemWrite dst src@ represents a write to @dst@ from the given source.
  = forall w. MemWrite (LLVMPtr sym w) (WriteSource sym w)
    -- | The merger of two memories.
  | WriteMerge (Pred sym) [MemWrite sym] [MemWrite sym]
