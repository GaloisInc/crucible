{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module TestMemory
  (
    memoryTests
  )
where

import           Control.Monad ( foldM, forM_, void )
import           Data.Foldable ( foldlM )
import qualified Data.Vector as V

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?), assertFailure )

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr ( knownNat )
import           Data.Parameterized.Nonce ( withIONonceGenerator )
import qualified What4.Expr.Builder as W4B
import qualified What4.Config as What4
import qualified What4.Interface as What4
import           What4.ProblemFeatures ( noFeatures )
import qualified What4.Protocol.Online as W4O
import qualified What4.SatResult as W4Sat

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Types as Crucible

import           Lang.Crucible.LLVM.DataLayout ( noAlignment )
import qualified Lang.Crucible.LLVM.DataLayout as LLVMD
import           Lang.Crucible.LLVM.MemModel ( doLoad, doStore, projectLLVM_bv, ptrAdd )
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Generic as LLVMMemG


memoryTests :: T.TestTree
memoryTests = T.testGroup "Memory"
  [
    testArrayStride
  , testMemAllocs
  , testMemWritesIndexed
  , testMemArrayWithConstants
  , testMemArray
  , testPointerStore
  , testMemArrayCopy
  , testMemArraySet
  , testMemInvalidate
  ]

data LLVMTestMemoryState t = LLVMTestMemoryState

withMem ::
  LLVMD.EndianForm ->
  (forall bak sym scope solver st fs wptr .
    ( sym ~ W4B.ExprBuilder scope st fs
    , bak ~ CBO.OnlineBackend solver scope st fs
    , CB.IsSymInterface sym
    , CB.IsBoolSolver sym bak
    , LLVMMem.HasLLVMAnn sym
    , W4O.OnlineSolver solver
    , LLVMMem.HasPtrWidth wptr
    , ?memOpts :: LLVMMem.MemOptions ) =>
    bak -> LLVMMem.MemImpl sym -> IO a) ->
  IO a
withMem endianess action = withIONonceGenerator $ \nonce_gen -> do
  sym <- W4B.newExprBuilder W4B.FloatIEEERepr LLVMTestMemoryState nonce_gen
  CBO.withZ3OnlineBackend sym CBO.NoUnsatFeatures noFeatures $ \bak -> do
    let ?ptrWidth = knownNat @64
    let ?recordLLVMAnnotation = \_ _ _ -> pure ()
    let ?memOpts = LLVMMem.defaultMemOptions
    mem <- LLVMMem.emptyMem endianess
    action bak mem

setCacheTerms :: CB.IsSymInterface sym => sym -> Bool ->IO ()
setCacheTerms sym cache_terms_option = do
  cache_terms_setting <- What4.getOptionSetting W4B.cacheTerms $ What4.getConfiguration sym
  void $ What4.setOpt cache_terms_setting cache_terms_option

userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

assume :: (CB.IsSymInterface sym, CB.IsBoolSolver sym bak) => bak -> What4.Pred sym -> IO ()
assume bak p = do
  let sym = CB.backendGetSym bak
  loc <- What4.getCurrentProgramLoc sym
  CB.addAssumption bak (CB.GenericAssumption loc "assume" p)

checkSat ::
  W4O.OnlineSolver solver =>
  CBO.OnlineBackend solver scope st fs ->
  W4B.BoolExpr scope ->
  IO (W4Sat.SatResult () ())
checkSat bak p =
  let err = fail "Online solving not enabled!" in
  CBO.withSolverProcess bak err $ \proc ->
     W4O.checkSatisfiable proc "" p


testArrayStride :: T.TestTree
testArrayStride = testCase "array stride" $ withMem LLVMD.BigEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak
  sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (1024 * 1024)
  (base_ptr, mem1) <- LLVMMem.mallocRaw bak mem0 sz noAlignment

  let byte_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @8
  let byte_storage_type = LLVMMem.bitvectorType 1
  let ptr_byte_repr = LLVMMem.LLVMPointerRepr $ knownNat @8

  init_array_val <- LLVMMem.LLVMValArray byte_storage_type <$>
    V.generateM (1024 * 1024)
      (\i -> LLVMMem.packMemValue sym byte_storage_type byte_type_repr
        =<< What4.bvLit sym (knownNat @8) (BV.mkBV knownNat (fromIntegral (mod i (512 * 1024)))))
  mem2 <- LLVMMem.storeRaw
    bak
    mem1
    base_ptr
    (LLVMMem.arrayType (1024 * 1024) byte_storage_type)
    noAlignment
    init_array_val

  stride <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (512 * 1024)

  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  ptr_i <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvMul sym stride i
  ptr_i' <- ptrAdd sym ?ptrWidth ptr_i =<< What4.bvLit sym ?ptrWidth (BV.one ?ptrWidth)

  zero_bv <- What4.bvLit sym (knownNat @8) (BV.zero knownNat)
  mem3 <-
    doStore bak mem2 ptr_i byte_type_repr byte_storage_type noAlignment zero_bv
  one_bv <- What4.bvLit sym (knownNat @8) (BV.one knownNat)
  mem4 <-
    doStore bak mem3 ptr_i' byte_type_repr byte_storage_type noAlignment one_bv

  at_0_val <- projectLLVM_bv bak
    =<< doLoad bak mem4 base_ptr byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.zero knownNat)) @=? What4.asBV at_0_val

  j <- What4.freshConstant sym (userSymbol' "j") $ What4.BaseBVRepr ?ptrWidth
  ptr_j <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvMul sym stride j
  ptr_j' <- ptrAdd sym ?ptrWidth ptr_j =<< What4.bvLit sym ?ptrWidth (BV.one ?ptrWidth)

  at_j_val <- projectLLVM_bv bak
    =<< doLoad bak mem4 ptr_j byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.zero knownNat)) @=? What4.asBV at_j_val

  at_j'_val <- projectLLVM_bv bak
    =<< doLoad bak mem4 ptr_j' byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.one knownNat)) @=? What4.asBV at_j'_val


allocFreshArray ::
  ( CB.IsSymInterface sym, CB.IsBoolSolver sym bak, LLVMMem.HasLLVMAnn sym, LLVMMem.HasPtrWidth wptr
  , ?memOpts :: LLVMMem.MemOptions ) =>
  bak ->
  LLVMMem.MemImpl sym ->
  Integer ->
  IO (LLVMMem.LLVMPtr sym wptr, What4.SymArray sym (SingleCtx (What4.BaseBVType wptr)) (What4.BaseBVType 8), LLVMMem.MemImpl sym)
allocFreshArray bak mem sz = do
  let sym = CB.backendGetSym bak
  sz_bv <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth sz
  (base_ptr, mem1) <- LLVMMem.mallocRaw bak mem sz_bv noAlignment
  arr <- What4.freshConstant
    sym
    (userSymbol' "a")
    (What4.BaseArrayRepr (Ctx.singleton $ What4.BaseBVRepr ?ptrWidth) (What4.BaseBVRepr (knownNat @8)))
  mem2 <- LLVMMem.doArrayStore bak mem1 base_ptr noAlignment arr sz_bv
  return (base_ptr, arr, mem2)


-- | This test case verifies that the symbolic aspects of the SMT-backed array
-- memory model works (e.g., that constraints on symbolic indexes work as
-- expected)
testMemArray :: T.TestTree
testMemArray = testCase "smt array memory model" $ withMem LLVMD.BigEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak
  -- Make a fresh allocation (backed by a fresh SMT array) of size 1024*1024 bytes.
  -- The base pointer of the array is base_ptr
  sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (1024 * 1024)
  (base_ptr, mem1) <- LLVMMem.mallocRaw bak mem0 sz noAlignment

  arr <- What4.freshConstant
    sym
    (userSymbol' "a")
    (What4.BaseArrayRepr
      (Ctx.singleton $ What4.BaseBVRepr ?ptrWidth)
      (What4.BaseBVRepr (knownNat @8)))
  mem2 <- LLVMMem.doArrayStore bak mem1 base_ptr noAlignment arr sz

  let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
  let long_storage_type = LLVMMem.bitvectorType 8
  let ptr_long_repr = LLVMMem.LLVMPointerRepr $ knownNat @64

  -- Store a large known 8 byte value at a symbolic location in the array (at
  -- @i@ bytes from the beginning of the array).  The assumption constrains it
  -- such that the location is within the first 1024 bytes of the array.
  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  ptr_i <- ptrAdd sym ?ptrWidth base_ptr i
  assume bak =<< What4.bvUlt sym i =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  some_val <- What4.bvLit sym (knownNat @64) (BV.mkBV knownNat 0x88888888f0f0f0f0)
  mem3 <-
    doStore bak mem2 ptr_i long_type_repr long_storage_type noAlignment some_val

  memset_ptr <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 2048)
  memset_val <- What4.bvLit sym knownNat (BV.mkBV knownNat 0)
  memset_sz <- What4.bvLit sym (knownNat @64) (BV.mkBV knownNat 10)
  mem4 <- LLVMMem.doMemset bak (knownNat @64) mem3 memset_ptr memset_val memset_sz

  -- Read that same value back and make sure that they are the same
  at_i_val <- projectLLVM_bv bak
    =<< doLoad bak mem4 ptr_i long_storage_type ptr_long_repr noAlignment
  res_i <- checkSat bak =<< What4.bvNe sym some_val at_i_val
  True @=? W4Sat.isUnsat res_i

  -- Allocate another fresh arbitrary constant and add it to the base pointer.
  -- Assume that i = j, then verify that reading from j yields the same value as
  -- was written at i.
  j <- What4.freshConstant sym (userSymbol' "j") $ What4.BaseBVRepr ?ptrWidth
  ptr_j <- ptrAdd sym ?ptrWidth base_ptr j
  assume bak =<< What4.bvEq sym i j
  at_j_val <- projectLLVM_bv bak
    =<< doLoad bak mem4 ptr_j long_storage_type ptr_long_repr noAlignment
  res_j <- checkSat bak =<< What4.bvNe sym some_val at_j_val
  True @=? W4Sat.isUnsat res_j


-- | Like testMemArray, but using some concrete indexes in a few places.  This
-- test checks the implementation of saturated addition of two numbers.
--
-- This is simulating the use of an SMT array to represent a program stack, and
-- ensures that:
--
-- * Concrete indexing works as expected
-- * Goals that depend on the values of values stored in memory work
testMemArrayWithConstants :: T.TestTree
testMemArrayWithConstants = testCase "smt array memory model (with constant indexing)" $ do
  withMem LLVMD.LittleEndian $ \bak mem0 -> do
    let sym = CB.backendGetSym bak
    sz <- What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth (2 * 1024))
    (region_ptr, mem1) <- LLVMMem.mallocRaw bak mem0 sz noAlignment
    let mRepr = What4.BaseArrayRepr (Ctx.singleton (What4.BaseBVRepr ?ptrWidth)) (What4.BaseBVRepr (knownNat @8))
    backingArray <- What4.freshConstant sym (userSymbol' "backingArray") mRepr
    mem2 <- LLVMMem.doArrayStore bak mem1 region_ptr noAlignment backingArray sz

    let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
    let long_storage_type = LLVMMem.bitvectorType 8
    let ptr_long_repr = LLVMMem.LLVMPointerRepr $ knownNat @64

    -- Make our actual base pointer the middle of the stack, to simulate having
    -- some active frames above us
    base_off <- What4.freshConstant sym (userSymbol' "baseOffset") (What4.BaseBVRepr ?ptrWidth)
    assume bak =<< What4.bvUlt sym base_off =<< (What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 10))
    base_ptr <- ptrAdd sym ?ptrWidth region_ptr base_off -- =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)

    -- Assume we have two arguments to our virtual function:
    param_a <- What4.freshConstant sym (userSymbol' "paramA") (What4.BaseBVRepr (knownNat @64))
    param_b <- What4.freshConstant sym (userSymbol' "paramB") (What4.BaseBVRepr (knownNat @64))

    -- The fake stack frame will start at @sp@ be:
    --
    -- sp+8  : Stack slot for spilling a
    slot_a <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 8)
    -- sp+16 : Stack slot for spilling b
    slot_b <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 16)
    -- sp+24 : Stack slot for local variable c
    slot_c <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 24)

    -- Store a and b onto the stack
    mem3 <- doStore bak mem2 slot_a long_type_repr long_storage_type noAlignment param_a
    mem4 <- doStore bak mem3 slot_b long_type_repr long_storage_type noAlignment param_b

    -- Read a and b off of the stack and compute c = a+b (storing the result on the stack in c's slot)
    valA0 <- projectLLVM_bv bak =<< doLoad bak mem4 slot_a long_storage_type ptr_long_repr noAlignment
    valB0 <- projectLLVM_bv bak =<< doLoad bak mem4 slot_b long_storage_type ptr_long_repr noAlignment
    mem5 <- doStore bak mem4 slot_c long_type_repr long_storage_type noAlignment =<< What4.bvAdd sym valA0 valB0


    valA1 <- projectLLVM_bv bak =<< doLoad bak mem5 slot_a long_storage_type ptr_long_repr noAlignment
    valB1 <- projectLLVM_bv bak =<< doLoad bak mem5 slot_b long_storage_type ptr_long_repr noAlignment
    valC1 <- projectLLVM_bv bak =<< doLoad bak mem5 slot_c long_storage_type ptr_long_repr noAlignment

    -- Add some assumptions to make our assertion actually hold (i.e., avoiding overflow)
    let n64 = knownNat @64
    -- assume sym =<< What4.bvUlt sym param_a =<< What4.bvLit sym n64 (BV.mkBV n64 100)
    -- assume sym =<< What4.bvUlt sym param_b =<< What4.bvLit sym n64 (BV.mkBV n64 100)
    cLessThanA <- What4.bvSlt sym valC1 valA1
    cLessThanB <- What4.bvSlt sym valC1 valB1
    ifOverflow <- What4.orPred sym cLessThanA cLessThanB

    i64Max <- What4.bvLit sym n64 (BV.mkBV n64 0x7fffffffffffffff)
    clamped_c <- What4.bvIte sym ifOverflow i64Max valC1
    mem6 <- doStore bak mem5 slot_c long_type_repr long_storage_type noAlignment clamped_c

    valC2 <- projectLLVM_bv bak =<< doLoad bak mem6 slot_c long_storage_type ptr_long_repr noAlignment

    aLessThanC <- What4.bvSle sym param_a valC2
    bLessThanC <- What4.bvSle sym param_b valC2
    assertion <- What4.andPred sym aLessThanC bLessThanC
    goal <- What4.notPred sym assertion
    res <- checkSat bak goal
    True @=? W4Sat.isUnsat res


-- | This test case checks the memcpy aspect of the SMT-backed array memory model
testMemArrayCopy :: T.TestTree
testMemArrayCopy = testCase "smt array copy memory model" $ withMem LLVMD.LittleEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak

  setCacheTerms sym True

  (dst_base_ptr, dst_arr, mem1) <- allocFreshArray bak mem0 (1024 * 1024)
  (src_base_ptr, src_arr, mem2) <- allocFreshArray bak mem1 1024

  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  dst_ptr <- ptrAdd sym ?ptrWidth dst_base_ptr i
  assume bak =<< What4.bvUlt sym i =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  len <- What4.freshConstant sym (userSymbol' "l") $ What4.BaseBVRepr ?ptrWidth
  assume bak =<< What4.bvUlt sym len =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  mem3 <- LLVMMem.doMemcpy bak ?ptrWidth mem2 False dst_ptr src_base_ptr len

  zero_bv <- What4.bvLit sym ?ptrWidth $ BV.zero ?ptrWidth
  expected_arr <- What4.arrayCopy sym dst_arr i src_arr zero_bv len
  expected_val <- What4.arrayLookup sym expected_arr $ Ctx.singleton i

  actual_val <- projectLLVM_bv bak
    =<< doLoad bak mem3 dst_ptr (LLVMMem.bitvectorType 1) (LLVMMem.LLVMPointerRepr $ knownNat @8) noAlignment

  foo <- What4.bvEq sym expected_val actual_val
  (Just True) @=? What4.asConstantPred foo


-- | This test case checks the memset aspect of the SMT-backed array memory model
testMemArraySet :: T.TestTree
testMemArraySet = testCase "smt array copy memory model" $ withMem LLVMD.LittleEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak
  setCacheTerms sym True

  (base_ptr, arr, mem1) <- allocFreshArray bak mem0 (1024 * 1024)

  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  ptr_i <- ptrAdd sym ?ptrWidth base_ptr i
  assume bak =<< What4.bvUlt sym i =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  val <- What4.freshConstant sym (userSymbol' "v") $ What4.BaseBVRepr $ knownNat @8
  len <- What4.freshConstant sym (userSymbol' "l") $ What4.BaseBVRepr ?ptrWidth
  assume bak =<< What4.bvUlt sym len =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  mem3 <- LLVMMem.doMemset bak ?ptrWidth mem1 ptr_i val len

  expected_arr <- What4.arraySet sym arr i val len
  expected_val <- What4.arrayLookup sym expected_arr $ Ctx.singleton i

  actual_val <- projectLLVM_bv bak
    =<< doLoad bak mem3 ptr_i (LLVMMem.bitvectorType 1) (LLVMMem.LLVMPointerRepr $ knownNat @8) noAlignment

  foo <- What4.bvEq sym expected_val actual_val
  (Just True) @=? What4.asConstantPred foo


testMemWritesIndexed :: T.TestTree
testMemWritesIndexed = testCase "indexed memory writes" $ withMem LLVMD.BigEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak
  let count = 100 * 1000

  sz <- What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 8)
  (base_ptr1, mem1) <- LLVMMem.mallocRaw bak mem0 sz noAlignment
  (base_ptr2, mem2) <- LLVMMem.mallocRaw bak mem1 sz noAlignment

  let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
  let long_storage_type = LLVMMem.bitvectorType 8
  let ptr_long_repr = LLVMMem.LLVMPointerRepr $ knownNat @64

  zero_val <- What4.bvLit sym (knownNat @64) (BV.zero knownNat)
  mem3 <- doStore
    bak
    mem2
    base_ptr1
    long_type_repr
    long_storage_type
    noAlignment
    zero_val

  mem4 <- foldlM
    (\mem' i ->
      doStore bak mem' base_ptr2 long_type_repr long_storage_type noAlignment
        =<< What4.bvLit sym (knownNat @64) i)
    mem3
    (BV.enumFromToUnsigned (BV.zero (knownNat @64)) (BV.mkBV knownNat count))

  forM_ [0 .. count] $ \_ -> do
    val1 <- projectLLVM_bv bak
      =<< doLoad bak mem4 base_ptr1 long_storage_type ptr_long_repr noAlignment
    (Just (BV.zero knownNat)) @=? What4.asBV val1

  val2 <- projectLLVM_bv bak
    =<< doLoad bak mem4 base_ptr2 long_storage_type ptr_long_repr noAlignment
  (Just (BV.mkBV knownNat count)) @=? What4.asBV val2

testMemAllocs :: T.TestTree
testMemAllocs =
  testCase "memory model alloc/free" $
  withMem LLVMD.BigEndian $ \bak mem0 ->
  do let sym = CB.backendGetSym bak
     sz1 <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth 128
     sz2 <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth 72
     sz3 <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth 32
     (ptr1, mem1) <- LLVMMem.mallocRaw bak mem0 sz1 noAlignment
     (ptr2, mem2) <- LLVMMem.mallocRaw bak mem1 sz2 noAlignment
     mem3 <- LLVMMem.doFree bak mem2 ptr2
     (ptr3, mem4) <- LLVMMem.mallocRaw bak mem3 sz3 noAlignment
     mem5 <- LLVMMem.doFree bak mem4 ptr1
     mem6 <- LLVMMem.doFree bak mem5 ptr3

     let isAllocated = LLVMMem.isAllocatedAlignedPointer sym ?ptrWidth noAlignment LLVMMem.Mutable
     assertions <-
       sequence
       [ isAllocated ptr1 (Just sz1) mem1
       , isAllocated ptr1 (Just sz1) mem2
       , isAllocated ptr1 (Just sz1) mem3
       , isAllocated ptr1 (Just sz1) mem4
       , isAllocated ptr1 (Just sz1) mem5 >>= What4.notPred sym
       , isAllocated ptr1 (Just sz1) mem6 >>= What4.notPred sym

       , isAllocated ptr2 (Just sz2) mem1 >>= What4.notPred sym
       , isAllocated ptr2 (Just sz2) mem2
       , isAllocated ptr2 (Just sz2) mem3 >>= What4.notPred sym
       , isAllocated ptr2 (Just sz2) mem4 >>= What4.notPred sym
       , isAllocated ptr2 (Just sz2) mem5 >>= What4.notPred sym
       , isAllocated ptr2 (Just sz2) mem6 >>= What4.notPred sym

       , isAllocated ptr3 (Just sz3) mem1 >>= What4.notPred sym
       , isAllocated ptr3 (Just sz3) mem2 >>= What4.notPred sym
       , isAllocated ptr3 (Just sz3) mem3 >>= What4.notPred sym
       , isAllocated ptr3 (Just sz3) mem4
       , isAllocated ptr3 (Just sz3) mem5
       , isAllocated ptr3 (Just sz3) mem6 >>= What4.notPred sym
       ]
     assertion <- foldM (What4.andPred sym) (What4.truePred sym) assertions
     res <- checkSat bak =<< What4.notPred sym assertion
     True @=? W4Sat.isUnsat res

-- | This test case checks that 'doInvalidate' behaves as expected with and
-- without 'laxLoadsAndStores' enabled.
testMemInvalidate :: T.TestTree
testMemInvalidate =
  testCase "memory invalidation" $ withMem LLVMD.BigEndian $ \bak mem0 ->
  do let sym = CB.backendGetSym bak
     sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth 64
     let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
         long_storage_type = LLVMMem.bitvectorType 8
     zero_val <- What4.bvLit sym (knownNat @64) (BV.zero knownNat)

     let withInvalidatedReadVal memOpts k = do
           let ?memOpts = memOpts
           -- First, allocate some memory on the stack...
           (ptr, mem1) <- LLVMMem.doAlloca bak mem0 sz noAlignment "<alloca>"
           -- ...write some value to it (the exact value is unimportant)...
           mem2 <- LLVMMem.doStore bak mem1 ptr
                                   long_type_repr long_storage_type
                                   noAlignment zero_val
           -- ...invalidate the memory...
           mem3 <- LLVMMem.doInvalidate bak ?ptrWidth mem2 ptr "<invalidate>" sz
           -- ...and finally, read from the invalidated memory.
           partVal <- LLVMMemG.readMem sym ?ptrWidth Nothing ptr
                                       long_storage_type noAlignment
                                       (LLVMMem.memImplHeap mem3)
           k partVal

         testLaxInvalidatedRead :: String -> LLVMMem.IndeterminateLoadBehavior -> IO ()
         testLaxInvalidatedRead stability indeterminateLoadBehavior =
           withInvalidatedReadVal (?memOpts{ LLVMMem.laxLoadsAndStores = True
                                           , LLVMMem.indeterminateLoadBehavior = indeterminateLoadBehavior
                                           }) $ \partVal ->
           case partVal of
             LLVMMem.NoErr p _val -> do
               res <- checkSat bak p
               True @=? W4Sat.isSat res
             LLVMMem.Err p -> assertFailure $ unlines
               [ "Reading from invalidated, " ++ stability ++ "-symbolic memory unexpectedly failed"
               , "Predicate: " ++ show p
               ]

     -- Test with laxLoadsAndStores disabled, where reading from invalidated
     -- memory should result in an error.
     withInvalidatedReadVal (?memOpts{LLVMMem.laxLoadsAndStores = False}) $ \partVal ->
       case partVal of
         LLVMMem.Err p -> do
           res <- checkSat bak p
           True @=? W4Sat.isUnsat res
         LLVMMem.NoErr p val -> assertFailure $ unlines
           [ "Reading from invalidated memory unexpectedly succeeded"
           , "Predicate: " ++ show p
           , "LLVM value read: " ++ show val
           ]

     -- Test with laxLoadsAndStores enabled, using both the
     -- StableSymbolic and UnstableSymbolic settings for
     -- indeterminateLoadBehavior. Here, reading from invalidated memory should succeed.
     testLaxInvalidatedRead "stable" LLVMMem.StableSymbolic
     testLaxInvalidatedRead "unstable" LLVMMem.UnstableSymbolic

-- | Test storing and retrieving pointer in an SMT-backed array memory model
testPointerStore :: T.TestTree
testPointerStore = testCase "pointer store" $ withMem LLVMD.BigEndian $ \bak mem0 -> do
  let sym = CB.backendGetSym bak
  -- Allocate two blocks
  sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (1024 * 1024)
  (base_ptr1, _) <- LLVMMem.mallocRaw bak mem0 sz noAlignment
  (base_ptr2, block2_mem1) <- LLVMMem.mallocRaw bak mem0 sz noAlignment

  -- Store the first base pointer in the second block
  let pointer_storage_type = LLVMMem.bitvectorType 8
  let base_ptr1_val = LLVMMem.ptrToPtrVal base_ptr1
  block2_mem2 <- LLVMMem.storeRaw bak
                                  block2_mem1
                                  base_ptr2
                                  pointer_storage_type
                                  noAlignment
                                  base_ptr1_val
  -- Read the pointer back
  base_ptr1_back <- LLVMMem.loadRaw sym
                                    block2_mem2
                                    base_ptr2
                                    pointer_storage_type
                                    noAlignment

  -- Assert that the read pointer is equal to the original pointer
  base_ptr1_back_safe <- LLVMMem.assertSafe bak base_ptr1_back
  is_equal <- LLVMMem.testEqual sym base_ptr1_val base_ptr1_back_safe
  case is_equal of
    Nothing -> assertFailure "testEqual failed"
    Just p -> do
      goal <- What4.notPred sym p
      res <- checkSat bak goal
      True @=? W4Sat.isUnsat res
