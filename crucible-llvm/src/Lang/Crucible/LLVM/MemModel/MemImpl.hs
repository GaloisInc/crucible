-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.MemImpl
-- Description      : Implementation of the memory model interface
-- Copyright        : (c) Galois, Inc 2011-2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE ExistentialQuantification #-}

module Lang.Crucible.LLVM.MemModel.MemImpl
  ( MemImpl(..)
  , SomePointer(..)
  , GlobalMap
  , emptyMem
  , memEndian

  -- ** Printing
  , ppMem
  , doDumpMem

  -- ** Blocks
  , BlockSource(..)
  , nextBlock
  ) where

import           Data.Dynamic
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           System.IO (Handle, hPutStrLn)

import           Lang.Crucible.LLVM.DataLayout (EndianForm(..))
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Types

import qualified Text.LLVM.AST as L

import           What4.Interface (IsExprBuilder)

-- | A pointer with an existentially-quantified width
data SomePointer sym = forall w. SomePointer !(LLVMPtr sym w)

newtype BlockSource = BlockSource (IORef Integer)
type GlobalMap sym = Map L.Symbol (SomePointer sym)

nextBlock :: BlockSource -> IO Integer
nextBlock (BlockSource ref) =
  atomicModifyIORef' ref (\n -> (n+1, n))

-- | The implementation of an LLVM memory, containing an
-- allocation-block source, global map, handle map, and heap.
data MemImpl sym =
  MemImpl
  { memImplBlockSource :: BlockSource
  , memImplGlobalMap   :: GlobalMap sym
  , memImplHandleMap   :: Map Integer Dynamic
  , memImplHeap        :: G.Mem sym
  }

memEndian :: MemImpl sym -> EndianForm
memEndian = G.memEndian . memImplHeap

-- | Produce a fresh empty memory.
--   NB, we start counting allocation blocks at '1'.
--   Block number 0 is reserved for representing raw bitvectors.
emptyMem :: EndianForm -> IO (MemImpl sym)
emptyMem endianness = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty (G.emptyMem endianness)

ppMem :: IsExprBuilder sym => MemImpl sym -> Doc
ppMem mem = G.ppMem (memImplHeap mem)

-- | Pretty print a memory state to the given handle.
doDumpMem :: IsExprBuilder sym => Handle -> MemImpl sym -> IO ()
doDumpMem h mem = do
  hPutStrLn h (show (ppMem mem))
