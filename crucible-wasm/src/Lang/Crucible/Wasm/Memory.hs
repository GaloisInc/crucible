{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lang.Crucible.Wasm.Memory where

import Data.Bits
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy as LBS
import Numeric.Natural
import Data.Parameterized.Context

import Lang.Crucible.Backend
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.Intrinsics
import Lang.Crucible.Types

import qualified Language.Wasm.Structure as Wasm

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout (EndianForm(..), noAlignment)
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial

import What4.Interface
import What4.InterpretedFloatingPoint

import Lang.Crucible.Wasm.Utils

type WasmMem = IntrinsicType "Wasm_Mem" EmptyCtx

-- | 64Ki, the number of bytes in a memory page, as defined
--   by the WebAssembly spec.
pageSize :: BV.BV 32
pageSize = BV.word32 (64 * 1024)

-- | 2^16 is the absolute maximum number of pages that can
--   be allocated in a Wasm memory.
maxPages :: BV.BV 32
maxPages = BV.word32 (bit 16)

-- | Implicit allocation number of the memory base pointer
basePointer :: Natural
basePointer = 1

freshMemory :: IsSymInterface sym => sym -> Wasm.Limit -> IO (WasmMemImpl sym)
freshMemory sym lim =
  do (lo,hi) <- checkLim sym lim

     -- allocate an entire 32-bit address space in little endian mode
     let heap0 = G.emptyMem LittleEndian
     let heap1 = G.allocMem @32 G.GlobalAlloc basePointer Nothing noAlignment G.Mutable "" heap0

     -- clear the entire memory space by writing a constant array with the zero byte
     z32  <- bvLit sym knownNat (BV.word32 0)
     base <- natLit sym basePointer
     let bp = LLVMPointer base z32

     z8   <- bvLit sym knownNat (BV.word8 0)
     zArr <- constantArray sym (Empty :> BaseBVRepr (knownNat @32)) z8
     (heap,_,_) <- G.writeArrayMem sym (knownNat @32) bp noAlignment zArr Nothing heap1

     pure WasmMemImpl
          { wasmMemHeap = heap
          , wasmMemSize = lo
          , wasmMemMax  = hi
          }

checkLim :: IsSymInterface sym => sym -> Wasm.Limit -> IO (SymBV sym 32, SymBV sym 32)
checkLim sym (Wasm.Limit lo Nothing)
  | lo <= bit 16
  = do lo' <- bvLit sym knownNat (BV.mkBV knownNat (fromIntegral lo))
       hi' <- bvLit sym knownNat maxPages
       pure (lo',hi')

checkLim sym (Wasm.Limit lo (Just hi))
  | lo <= hi && hi <= bit 16
  = do lo' <- bvLit sym knownNat (BV.mkBV knownNat (fromIntegral lo))
       hi' <- bvLit sym knownNat (BV.mkBV knownNat (fromIntegral hi))
       pure (lo',hi')

checkLim _sym lim =
  panic "checkLim" ["invalid limit: " ++ show lim]


assertInBounds :: (IsSymBackend sym bak) => bak -> SymBV sym 32 -> Bytes -> WasmMemImpl sym -> IO ()

assertInBounds bak off (Bytes 0) mem = -- TODO? maybe should be an error condition instead?
  do let sym = backendGetSym bak
     offPageNum <- bvUdiv sym off =<< bvLit sym knownNat pageSize
     lt <- bvUlt sym offPageNum (wasmMemSize mem)
     assert bak lt (GenericSimError "pointer out of bounds")

assertInBounds bak off (Bytes n) mem =
  do let sym = backendGetSym bak
     end <- bvAdd sym off =<< bvLit sym knownNat (BV.mkBV knownNat (n-1))

     -- check that the addition didn't overflow
     le <- bvUle sym off end

     endPageNum <- bvUdiv sym off =<< bvLit sym knownNat pageSize
     endlt <- bvUlt sym endPageNum (wasmMemSize mem)

     ok <- andPred sym le endlt
     assert bak ok (GenericSimError "pointer out of bounds")

wasmGrowMem ::
  (IsSymBackend sym bak) =>
  bak ->
  SymBV sym 32 ->
  WasmMemImpl sym ->
  IO (SymBV sym 32, WasmMemImpl sym)
wasmGrowMem bak n mem =
  do let sym = backendGetSym bak
     (ov,newsz) <- addUnsignedOF sym n (wasmMemSize mem)
     le <- bvUle sym newsz (wasmMemMax mem)
     ok <- andPred sym le =<< notPred sym ov

     neg1 <- bvLit sym knownNat (BV.int32 (-1))

     newsz' <- bvIte sym ok newsz (wasmMemSize mem)
     res    <- bvIte sym ok newsz neg1

     let mem' = mem{ wasmMemSize = newsz' }

     return (res, mem')

wasmStoreChunk ::
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  LBS.ByteString ->
  WasmMemImpl sym ->
  IO (WasmMemImpl sym)
wasmStoreChunk bak offset chunk mem =
  do let sym = backendGetSym bak
     let bs = Bytes (toInteger (LBS.length chunk))
     assertInBounds bak offset bs mem
     p <- mkPtr sym offset
     let val = LLVMValString (LBS.toStrict chunk)
     let storageType = arrayType (fromIntegral (LBS.length chunk)) (bitvectorType (Bytes 1))
     (heap',_,_) <- G.writeMem sym knownNat Nothing p storageType noAlignment val (wasmMemHeap mem)
     return mem{ wasmMemHeap = heap' }


wasmStoreInt ::
  (1 <= w, IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  SymBV sym w ->
  WasmMemImpl sym ->
  IO (WasmMemImpl sym)
wasmStoreInt bak off v mem =
  do let sym = backendGetSym bak
     let bs = Bytes (intValue (bvWidth v) `div` 8)
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     blk <- natLit sym 0
     let val = LLVMValInt blk v
     (heap',_,_) <- G.writeMem sym knownNat Nothing p (bitvectorType bs) noAlignment val (wasmMemHeap mem)
     return mem{ wasmMemHeap = heap' }

wasmStoreFloat ::
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  RegValue sym (FloatType SingleFloat) ->
  WasmMemImpl sym ->
  IO (WasmMemImpl sym)
wasmStoreFloat bak off v mem =
  do let sym = backendGetSym bak
     let bs = Bytes 4
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     let val = LLVMValFloat SingleSize v
     (heap',_,_) <- G.writeMem sym knownNat Nothing p floatType noAlignment val (wasmMemHeap mem)
     return mem{ wasmMemHeap = heap' }

wasmStoreDouble ::
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  RegValue sym (FloatType DoubleFloat) ->
  WasmMemImpl sym ->
  IO (WasmMemImpl sym)
wasmStoreDouble bak off v mem =
  do let sym = backendGetSym bak
     let bs = Bytes 8
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     let val = LLVMValFloat DoubleSize v
     (heap',_,_) <- G.writeMem sym knownNat Nothing p doubleType noAlignment val (wasmMemHeap mem)
     return mem{ wasmMemHeap = heap' }

wasmLoadInt ::
  ( 1 <= w, IsSymBackend sym bak, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  SymBV sym 32 ->
  NatRepr w ->
  WasmMemImpl sym ->
  IO (SymBV sym w)
wasmLoadInt bak off w mem =
  do let sym = backendGetSym bak
     let bs = Bytes (intValue w `div` 8)
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     pval <- G.readMem sym knownNat Nothing p (bitvectorType bs) noAlignment (wasmMemHeap mem)
     Partial.assertSafe bak pval >>= \case
       LLVMValZero _ -> bvLit sym w (BV.zero w)
       LLVMValInt _ v | Just Refl <- testEquality (bvWidth v) w -> pure v
       _ -> panic "wasmLoadInt" ["type mismatch"]

wasmLoadFloat ::
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  WasmMemImpl sym ->
  IO (RegValue sym (FloatType SingleFloat))
wasmLoadFloat bak off mem =
  do let sym = backendGetSym bak
     let bs = Bytes 4
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     pval <- G.readMem sym knownNat Nothing p floatType noAlignment (wasmMemHeap mem)
     Partial.assertSafe bak pval >>= \case
       LLVMValZero _ -> iFloatLitRational sym SingleFloatRepr 0
       LLVMValFloat SingleSize v -> pure v
       _ -> panic "wasmLoadFloat" ["type mismatch"]

wasmLoadDouble ::
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  SymBV sym 32 ->
  WasmMemImpl sym ->
  IO (RegValue sym (FloatType DoubleFloat))
wasmLoadDouble bak off mem =
  do let sym = backendGetSym bak
     let bs = Bytes 8
     assertInBounds bak off bs mem
     p <- mkPtr sym off
     pval <- G.readMem sym knownNat Nothing p doubleType noAlignment (wasmMemHeap mem)
     Partial.assertSafe bak pval >>= \case
       LLVMValZero _ -> iFloatLitRational sym DoubleFloatRepr 0
       LLVMValFloat DoubleSize v -> pure v
       _ -> panic "wasmLoadDouble" ["type mismatch"]


mkPtr :: IsSymInterface sym => sym -> SymBV sym 32 -> IO (LLVMPtr sym 32)
mkPtr sym off =
  do blk <- natLit sym basePointer
     pure (LLVMPointer blk off)

data WasmMemImpl sym =
  WasmMemImpl
  { wasmMemHeap    :: !(G.Mem sym)
      -- ^ main heap datastructure
  , wasmMemSize    :: !(SymBV sym 32)
      -- ^ number of data pages in this memory
  , wasmMemMax     :: !(SymBV sym 32)
      -- ^ maximum number of pages this memory can grow to
  }

instance IsSymInterface sym => IntrinsicClass sym "Wasm_Mem" where
  type Intrinsic sym "Wasm_Mem" ctx = WasmMemImpl sym

  muxIntrinsic sym _ _nm _ctx p mem1 mem2 =
    do let WasmMemImpl heap1 sz1 mx1 = mem1
       let WasmMemImpl heap2 sz2 mx2 = mem2
       sz <- bvIte sym p sz1 sz2
       mx <- bvIte sym p mx1 mx2
       return $ WasmMemImpl (G.mergeMem p heap1 heap2) sz mx

  pushBranchIntrinsic _sym _iTypes _nm _ctx mem =
    do let WasmMemImpl heap sz mx = mem
       return $ WasmMemImpl (G.branchMem heap) sz mx

  abortBranchIntrinsic _sym _iTypes _nm _ctx mem =
    do let WasmMemImpl heap sz mx = mem
       return $ WasmMemImpl (G.branchAbortMem heap) sz mx
