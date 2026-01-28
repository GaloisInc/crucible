-- TODO(#1406): Move the definitions of the deprecated imports into this module,
-- and remove the exports from MemModel.
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Manipulating C-style null-terminated strings
module Lang.Crucible.LLVM.MemModel.Strings
  ( storeString
  -- * Loading strings
  , Mem.loadString
  , Mem.loadMaybeString
  , loadConcretelyNullTerminatedString
  , loadProvablyNullTerminatedString
  -- * String length
  , Mem.strLen
  , strnlen
  , strlenConcreteString
  , strlenConcretelyNullTerminatedString
  , strlenProvablyNullTerminatedString
  -- * String copying
  , copyConcreteString
  , copyConcretelyNullTerminatedString
  , copyProvablyNullTerminatedString
  -- * String duplication
  , dupConcreteString
  , dupConcretelyNullTerminatedString
  , dupProvablyNullTerminatedString
  -- * Memory comparison
  , memcmp
  , memcmpConcreteLen
  -- * String comparison
  , strncmp
  , strncmpConcreteLen
  , cmpConcreteString
  , cmpConcretelyNullTerminatedString
  , cmpProvablyNullTerminatedString
  -- * Low-level string loading primitives
  -- ** 'ByteChecker'
  , ControlFlow(..)
  , ByteChecker(..)
  , withMaxChars
  -- *** For loading strings
  , fullyConcreteNullTerminatedString
  , concretelyNullTerminatedString
  , provablyNullTerminatedString
  -- *** For string length
  , fullyConcreteNullTerminatedStringLength
  , concretelyNullTerminatedStringLength
  , provablyNullTerminatedStringLength
  -- ** 'ByteLoader'
  , ByteLoader(..)
  , llvmByteLoader
  -- * 'loadBytes'
  , loadBytes
  -- * Loading and checking two byte streams
  -- ** 'BytesLoader'
  , BytesLoader(..)
  , llvmBytesLoader
  , llvmStringsLoader
  -- ** 'BytesChecker'
  , BytesChecker(..)
  , withMaxBytes
  -- ** 'loadTwoBytes'
  , loadTwoBytes
  -- ** 'BytesChecker's for string comparison
  , fullyConcreteNullTerminatedStrings
  , concretelyNullTerminatedStrings
  , provablyNullTerminatedStrings
  , lengthBoundedStringComparison
  , lengthBoundedProvablyNullTerminatedStringComparison
  -- ** 'BytesChecker's for length-bounded comparison
  , simpleByteComparison
  , lengthBoundedByteComparison
  ) where

import           Control.Lens ((^.), to)
import           Data.Bifunctor (Bifunctor(bimap))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Control.Monad.State.Strict as State
import qualified Data.BitVector.Sized as BV
import           Data.Functor ((<&>))
import qualified Data.Parameterized.NatRepr as DPN
import           Data.Word (Word8)
import qualified Data.Vector as Vec
import qualified GHC.Stack as GHC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemErr
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified Lang.Crucible.LLVM.MemModel.Generic as Mem.G
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.SatResult as WS

-- | Store a null-terminated string to memory.
storeNullTerminatedString ::
  forall sym bak w.
  ( LCB.IsSymBackend sym bak
  , WI.IsExpr (WI.SymExpr sym)
  , LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  -- | Pointer to write string to
  LCLM.LLVMPtr sym w ->
  -- | The bytes of the string to write (null terminator included)
  Vec.Vector (WI.SymBV sym 8) ->
  IO (LCLM.MemImpl sym)
storeNullTerminatedString bak mem ptr bytesBvs = do
  let sym = LCB.backendGetSym bak
  zeroNat <- WI.natLit sym 0
  let bytes = Vec.map (Mem.LLVMValInt zeroNat) bytesBvs
  let val = Mem.LLVMValArray (Mem.bitvectorType 1) bytes
  let storTy = Mem.llvmValStorableType @sym val
  Mem.storeRaw bak mem ptr storTy CLD.noAlignment val

-- | Store a string to memory, adding a null terminator at the end.
storeString ::
  forall sym bak w.
  ( LCB.IsSymBackend sym bak
  , WI.IsExpr (WI.SymExpr sym)
  , LCLM.HasPtrWidth w
  , LCLM.HasLLVMAnn sym
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  LCLM.MemImpl sym ->
  -- | Pointer to write string to
  LCLM.LLVMPtr sym w ->
  -- | The bytes of the string to write (null terminator not included)
  Vec.Vector (WI.SymBV sym 8) ->
  IO (LCLM.MemImpl sym)
storeString bak mem ptr bytesBvs = do
  let sym = LCB.backendGetSym bak
  zeroByte <- WI.bvZero sym (DPN.knownNat @8)
  let nullTerminatedBytes = Vec.snoc bytesBvs zeroByte
  storeNullTerminatedString bak mem ptr nullTerminatedBytes

---------------------------------------------------------------------
-- * Loading strings

-- | Load a null-terminated string (with a concrete null terminator) from memory.
--
-- The string must contain a concrete null terminator. If a maximum number of
-- characters is provided, no more than that number of characters will be read.
-- In either case, 'loadConcretelyNullTerminatedString' will stop reading if it
-- encounters a (concretely) null terminator.
--
-- Note that the loaded string may actually be smaller than the returned list if
-- any of the symbolic bytes are equal to 0.
loadConcretelyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO [WI.SymBV sym 8]
loadConcretelyNullTerminatedString bak mem ptr limit =
  let loader = llvmByteLoader mem in
  case limit of
    Nothing -> loadBytes bak mem id ptr loader concretelyNullTerminatedString
    Just l ->
      let byteChecker = withMaxChars l (\f -> pure (f [])) concretelyNullTerminatedString in
      loadBytes bak mem (id, 0) ptr loader byteChecker

-- | Load a null-terminated string from memory.
--
-- Consults an SMT solver to check if any of the loaded bytes are known
-- to be null (0). If a maximum number of characters is provided, no
-- more than that number of charcters will be read. In either case,
-- 'loadProvablyNullTerminatedString' will stop reading if it encounters a null
-- terminator.
--
-- Note that the loaded string may actually be smaller than the returned list if
-- any of the symbolic bytes are equal to 0.
loadProvablyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO [WI.SymBV sym 8]
loadProvablyNullTerminatedString bak mem ptr limit =
  let loader = llvmByteLoader mem in
  case limit of
    Nothing -> loadBytes bak mem id ptr loader provablyNullTerminatedString
    Just l ->
      let byteChecker = withMaxChars l (\f -> pure (f [])) provablyNullTerminatedString in
      loadBytes bak mem (id, 0) ptr loader byteChecker

---------------------------------------------------------------------
-- * String length

-- | Implementation of libc @strnlen@.
strnlen ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Pointer to null-terminated string
  Mem.LLVMPtr sym wptr ->
  -- | Size
  --
  -- If this is not concrete, this will generate an assertion failure.
  WI.SymBV sym wptr ->
  IO (WI.SymBV sym wptr)
strnlen bak mem ptr bound = do
  case BV.asUnsigned <$> WI.asBV bound of
    Nothing ->
      let err = LCS.AssertFailureSimError "`strnlen` called with symbolic max length" "" in
      LCB.addFailedAssertion bak err
    Just b ->
      let bound' = Just (fromIntegral b) in
      strlenConcretelyNullTerminatedString bak mem ptr bound'
 
-- | @strlen@ of a concrete string.
--
-- If any symbolic bytes are encountered, an assertion failure will be
-- generated. If a maximum number of characters is provided, no more than that
-- number of characters will be read. In either case, 'strlenConcreteString'
-- will stop reading if it encounters a null terminator.
strlenConcreteString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO Int
strlenConcreteString bak mem ptr limit = do
  let loader = llvmByteLoader mem
  case limit of
    Nothing -> loadBytes bak mem 0 ptr loader fullyConcreteNullTerminatedStringLength
    Just 0 -> pure 0
    Just l -> do
      let byteChecker = withMaxChars l pure fullyConcreteNullTerminatedStringLength
      loadBytes bak mem (0, 0) ptr loader byteChecker
 
-- | @strlen@ of a null-terminated string (with a concrete null terminator).
--
-- The string must contain a concrete null terminator. If a maximum number of
-- characters is provided, no more than that number of characters will be read.
-- In either case, 'strlenConcretelyNullTerminatedString' will stop reading if
-- it encounters a (concretely) null terminator.
--
-- This has the same behavior as 'Lang.Crucible.LLVM.MemModel.strLen', except
-- that it supports a maximum length.
strlenConcretelyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO (WI.SymBV sym wptr)
strlenConcretelyNullTerminatedString bak mem ptr limit = do
  let loader = llvmByteLoader mem
  let sym = LCB.backendGetSym bak
  z <- WI.bvZero sym ?ptrWidth
  flip State.evalStateT (WI.truePred sym) $
    case limit of
      Nothing -> loadBytes bak mem z ptr loader concretelyNullTerminatedStringLength
      Just 0 -> liftIO (WI.bvZero (LCB.backendGetSym bak) ?ptrWidth)
      Just l -> do
        let byteChecker = withMaxChars l pure concretelyNullTerminatedStringLength
        loadBytes bak mem (z, 0) ptr loader byteChecker

-- | @strlen@ of a provably null-terminated string.
--
-- Consults an SMT solver to check if any of the loaded bytes are known
-- to be null (0). If a maximum number of characters is provided, no
-- more than that number of charcters will be read. In either case,
-- 'strlenProvablyNullTerminatedString' will stop reading if it encounters a
-- (provably) null terminator.
strlenProvablyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO (WI.SymBV sym wptr)
strlenProvablyNullTerminatedString bak mem ptr limit = do
  let loader = llvmByteLoader mem
  let sym = LCB.backendGetSym bak
  z <- WI.bvZero sym ?ptrWidth
  flip State.evalStateT (WI.truePred sym) $
    case limit of
      Nothing -> loadBytes bak mem z ptr loader provablyNullTerminatedStringLength
      Just 0 -> liftIO (WI.bvZero (LCB.backendGetSym bak) ?ptrWidth)
      Just l -> do
        let byteChecker = withMaxChars l pure provablyNullTerminatedStringLength
        loadBytes bak mem (z, 0) ptr loader byteChecker

---------------------------------------------------------------------
-- * String copying

-- | Helper, not exported
strcpyAssertDisjoint ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Loaded bytes
  Vec.Vector (WI.SymBV sym 8) ->
  -- | Destination pointer
  Mem.LLVMPtr sym wptr ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  IO ()
strcpyAssertDisjoint bak mem bytes dst src = do
  let sym = LCB.backendGetSym bak
  let len = fromIntegral (Vec.length bytes)
  sz <- WI.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth len)
  let heap = mem ^. to Mem.memImplHeap
  let memOp =
        MemErr.MemCopyOp (Just "strcpy dst", dst) (Just "strcpy src", src) sz heap
  Mem.assertDisjointRegions bak memOp ?ptrWidth dst sz src sz

-- | @strcpy@ of a concrete string.
--
-- Uses 'Mem.loadString' to load the string, see that function for details.
--
-- Asserts that the regions are disjoint.
copyConcreteString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Destination pointer
  Mem.LLVMPtr sym wptr ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  IO (Mem.MemImpl sym)
copyConcreteString bak mem dst src = do
  bytes <- Mem.loadString bak mem src Nothing
  let sym = LCB.backendGetSym bak
  symBytes <- mapM (WI.bvLit sym WI.knownRepr . BV.word8) bytes
  let bytesVec = Vec.fromList symBytes
  strcpyAssertDisjoint bak mem bytesVec dst src
  storeString bak mem dst (Vec.fromList symBytes)

-- | @strcpy@ of a concretely null-terminated string.
--
-- Uses 'loadConcretelyNullTerminatedString' to load the string, see that
-- function for details.
--
-- Asserts that the regions are disjoint.
copyConcretelyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Destination pointer
  Mem.LLVMPtr sym wptr ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO (Mem.MemImpl sym)
copyConcretelyNullTerminatedString bak mem dst src bounds = do
  bytes <- loadConcretelyNullTerminatedString bak mem src bounds
  let bytesVec = Vec.fromList bytes
  strcpyAssertDisjoint bak mem bytesVec dst src
  storeString bak mem dst bytesVec

-- | @strcpy@ of a concrete string.
--
-- Uses 'loadProvablyNullTerminatedString' to load the string, see that
-- function for details.
--
-- Asserts that the regions are disjoint.
copyProvablyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Destination pointer
  Mem.LLVMPtr sym wptr ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO (Mem.MemImpl sym)
copyProvablyNullTerminatedString bak mem dst src bounds = do
  bytes <- loadProvablyNullTerminatedString bak mem src bounds
  let bytesVec = Vec.fromList bytes
  strcpyAssertDisjoint bak mem bytesVec dst src
  storeString bak mem dst bytesVec

---------------------------------------------------------------------
-- * String duplication

-- | Helper function: allocate memory and store bytes for string duplication.
--
-- Takes a vector of bytes (NOT including null terminator) and:
-- 1. Allocates memory of the appropriate size (length + 1 for null terminator)
-- 2. Stores the bytes with null terminator to the allocated memory
-- 3. Returns the new pointer and updated memory
dupFromLoadedBytes ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Vec.Vector (WI.SymBV sym 8) ->
  String ->
  CLD.Alignment ->
  IO (Mem.LLVMPtr sym wptr, Mem.MemImpl sym)
dupFromLoadedBytes bak mem bytesVec displayString alignment = do
  let len = fromIntegral (Vec.length bytesVec) + 1  -- +1 for null terminator
  let sym = LCB.backendGetSym bak
  sz <- WI.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth len)
  (dst, mem') <- Mem.doMalloc bak Mem.G.HeapAlloc Mem.G.Mutable displayString mem sz alignment
  mem'' <- storeString bak mem' dst bytesVec
  pure (dst, mem'')

-- | @strdup@ of a concrete string.
--
-- Uses 'Mem.loadString' to load the string, see that function for details.
--
-- Allocates memory and copies the string to it, returning the new pointer.
dupConcreteString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  -- | Display string for allocation
  String ->
  -- | Alignment
  CLD.Alignment ->
  IO (Mem.LLVMPtr sym wptr, Mem.MemImpl sym)
dupConcreteString bak mem src displayString alignment = do
  bytes <- Mem.loadString bak mem src Nothing
  let sym = LCB.backendGetSym bak
  symBytes <- mapM (WI.bvLit sym WI.knownRepr . BV.word8) bytes
  dupFromLoadedBytes bak mem (Vec.fromList symBytes) displayString alignment

-- | @strdup@ of a concretely null-terminated string.
--
-- Uses 'loadConcretelyNullTerminatedString' to load the string, see that
-- function for details.
--
-- Allocates memory and copies the string to it, returning the new pointer.
dupConcretelyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  -- | Display string for allocation
  String ->
  CLD.Alignment ->
  IO (Mem.LLVMPtr sym wptr, Mem.MemImpl sym)
dupConcretelyNullTerminatedString bak mem src bounds displayString alignment = do
  bytes <- loadConcretelyNullTerminatedString bak mem src bounds
  dupFromLoadedBytes bak mem (Vec.fromList bytes) displayString alignment

-- | @strdup@ of a provably null-terminated string.
--
-- Uses 'loadProvablyNullTerminatedString' to load the string, see that
-- function for details.
--
-- Allocates memory and copies the string to it, returning the new pointer.
dupProvablyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Source pointer
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to read
  Maybe Int ->
  -- | Display string for allocation
  String ->
  CLD.Alignment ->
  IO (Mem.LLVMPtr sym wptr, Mem.MemImpl sym)
dupProvablyNullTerminatedString bak mem src bounds displayString alignment = do
  bytes <- loadProvablyNullTerminatedString bak mem src bounds
  dupFromLoadedBytes bak mem (Vec.fromList bytes) displayString alignment

---------------------------------------------------------------------
-- * String comparison

-- | Compare two concrete strings.
--
-- Uses 'fullyConcreteNullTerminatedStrings' checker. Both strings must be
-- fully concrete (no symbolic bytes).
--
-- Returns:
-- * 0 if the strings are equal
-- * A negative value if the first differing byte in s1 is less than in s2
-- * A positive value if the first differing byte in s1 is greater than in s2
cmpConcreteString ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  IO (WI.SymBV sym 32)
cmpConcreteString bak mem ptr1 ptr2 = do
  let sym = LCB.backendGetSym bak
  zero <- WI.bvZero sym (DPN.knownNat @32)
  loadTwoBytes bak mem zero ptr1 ptr2 (llvmStringsLoader mem) fullyConcreteNullTerminatedStrings

-- | Compare two strings with concrete null terminators.
--
-- Uses 'concretelyNullTerminatedStrings' checker. The strings must have
-- concrete null terminators, but may contain symbolic bytes before the terminator.
--
-- If a maximum length is provided, comparison stops at that length even if
-- no null terminator is encountered.
--
-- Returns:
-- * 0 if the strings are equal
-- * A negative value if the first differing byte in s1 is less than in s2
-- * A positive value if the first differing byte in s1 is greater than in s2
cmpConcretelyNullTerminatedString ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to compare
  Maybe Int ->
  IO (WI.SymBV sym 32)
cmpConcretelyNullTerminatedString bak mem ptr1 ptr2 maxLen = do
  let sym = LCB.backendGetSym bak
  zero <- WI.bvZero sym (DPN.knownNat @32)
  case maxLen of
    Nothing ->
      loadTwoBytes bak mem zero ptr1 ptr2 (llvmStringsLoader mem) concretelyNullTerminatedStrings
    Just 0 ->
      WI.bvZero sym (DPN.knownNat @32)
    Just n ->
      loadTwoBytes bak mem (zero, 0) ptr1 ptr2 (llvmStringsLoader mem) (lengthBoundedStringComparison (fromIntegral n))

-- | Compare two strings with provably null terminators.
--
-- Uses 'provablyNullTerminatedStrings' checker. Consults an SMT solver to
-- check if bytes are provably null terminators.
--
-- If a maximum length is provided, comparison stops at that length even if
-- no null terminator is encountered.
--
-- Returns:
-- * 0 if the strings are equal
-- * A negative value if the first differing byte in s1 is less than in s2
-- * A positive value if the first differing byte in s1 is greater than in s2
cmpProvablyNullTerminatedString ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  -- | Maximum number of characters to compare
  Maybe Int ->
  IO (WI.SymBV sym 32)
cmpProvablyNullTerminatedString bak mem ptr1 ptr2 maxLen = do
  let sym = LCB.backendGetSym bak
  zero <- WI.bvZero sym (DPN.knownNat @32)
  case maxLen of
    Nothing ->
      loadTwoBytes bak mem zero ptr1 ptr2 (llvmStringsLoader mem) provablyNullTerminatedStrings
    Just 0 ->
      WI.bvZero sym (DPN.knownNat @32)
    Just n ->
      loadTwoBytes bak mem (zero, 0) ptr1 ptr2 (llvmStringsLoader mem) (lengthBoundedProvablyNullTerminatedStringComparison (fromIntegral n))

-- | @strncmp@ - compare two null-terminated strings up to n characters.
--
-- See 'strncmpConcreteLen' for the return value.
--
-- Asserts that the length is concrete (non-symbolic).
strncmp ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  WI.SymBV sym wptr ->
  IO (WI.SymBV sym 32)
strncmp bak mem ptr1 ptr2 len =
  case BV.asUnsigned <$> WI.asBV len of
    Just n -> strncmpConcreteLen bak mem ptr1 ptr2 (fromIntegral n)
    Nothing -> do
      let err = LCS.AssertFailureSimError "`strncmp` called with symbolic length" ""
      LCB.addFailedAssertion bak err

-- | Compare two null-terminated strings up to n characters with a concrete length.
--
-- Returns:
-- * 0 if the strings are equal (up to n characters or null terminator)
-- * A negative value if the first differing byte in s1 is less than in s2
-- * A positive value if the first differing byte in s1 is greater than in s2
--
-- Requires that both strings have concrete null terminators.
strncmpConcreteLen ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  Integer ->
  IO (WI.SymBV sym 32)
strncmpConcreteLen bak mem ptr1 ptr2 n =
  cmpConcretelyNullTerminatedString bak mem ptr1 ptr2 (Just (fromIntegral n))

---------------------------------------------------------------------
-- * Memory comparison

-- | @memcmp@.
--
-- See 'memcmpConcreteLen' for the return value.
--
-- Asserts that the length is concrete (non-symbolic).
memcmp ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  WI.SymBV sym wptr ->
  IO (WI.SymBV sym 32)
memcmp bak mem ptr1 ptr2 len =
  case BV.asUnsigned <$> WI.asBV len of
    Just n -> memcmpConcreteLen bak mem ptr1 ptr2 (fromIntegral n)
    Nothing -> do
      let err = LCS.AssertFailureSimError "`memcmp` called with symbolic length" ""
      LCB.addFailedAssertion bak err

-- | Compare two memory regions byte-by-byte with a concrete length.
--
-- Returns:
-- * 0 if the regions are equal
-- * A negative value if the first differing byte in s1 is less than in s2
-- * A positive value if the first differing byte in s1 is greater than in s2
memcmpConcreteLen ::
  forall sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  Mem.LLVMPtr sym wptr ->
  Integer ->
  IO (WI.SymBV sym 32)
memcmpConcreteLen bak mem ptr1 ptr2 n
  | n == 0 = do
      let sym = LCB.backendGetSym bak
      WI.bvZero sym (DPN.knownNat @32)
  | otherwise =
      loadTwoBytes bak mem ((), 0) ptr1 ptr2 (llvmBytesLoader mem) (lengthBoundedByteComparison n)

---------------------------------------------------------------------
-- * Low-level string loading primitives

---------------------------------------------------------------------
-- ** 'ByteChecker'

-- | Whether to stop or keep going
--
-- Like Rust's @std::ops::ControlFlow@.
data ControlFlow a b
  = Continue a
  | Break b
  deriving Functor

-- NB: 'first' is used in this module
instance Bifunctor ControlFlow where
  bimap l r =
    \case
      Continue x -> Continue (l x)
      Break x -> Break (r x)

-- | Compute a result from a symbolic byte, and check if the load should
-- continue to the next byte.
--
-- Used to:
--
-- * Check if the byte is concrete ('fullyConcreteNullTerminatedString')
-- * Check if the byte is concretely a null terminator
--   ('concretelyNullTerminatedString')
-- * Check if a byte is known by a solver to be a null terminator ('nullTerminatedString')
-- * Check if we have surpassed a length limit ('withMaxChars')
--
-- Note that it is relatively common for @a@ to be a function @[b] -> [b]@. This
-- is used to build up a snoc-list.
newtype ByteChecker m sym bak a b
  = ByteChecker { runByteChecker :: bak -> a -> Mem.LLVMPtr sym 8 -> m (ControlFlow a b) }

-- Helper, not exported
ptrToBv8 ::
  LCB.IsSymBackend sym bak =>
  bak ->
  Mem.LLVMPtr sym 8 ->
  IO (WI.SymBV sym 8)
ptrToBv8 bak bytePtr = do
  let err = LCS.AssertFailureSimError "Found pointer instead of byte when loading string" ""
  Partial.ptrToBv bak err bytePtr

-- | 'ByteChecker' for adding a maximum character length.
withMaxChars ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  Functor m =>
  -- | Maximum number of bytes to load
  Int ->
  -- | What to do when the maximum is reached
  (a -> m b) ->
  ByteChecker m sym bak a b ->
  ByteChecker m sym bak (a, Int) b
withMaxChars limit done checker =
  ByteChecker $ \bak (acc, i) bytePtr ->
    runByteChecker checker bak acc bytePtr >>=
      \case
        Break r -> pure (Break r)
        Continue r ->
          if i + 1 >= limit
          then Break <$> done r
          else pure (Continue (r, i + 1))

---------------------------------------------------------------------
-- *** For loading strings

-- | 'ByteChecker' for loading concrete strings.
--
-- Currently unused internally, but analogous with
-- 'Lang.Crucible.LLVM.MemModel.loadString'. In fact, it would be good to define
-- that function in terms of this one. However, this is blocked on TODO(#1406).
fullyConcreteNullTerminatedString ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  ByteChecker m sym bak ([Word8] -> [Word8]) [Word8]
fullyConcreteNullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- liftIO (ptrToBv8 bak bytePtr)
    case BV.asUnsigned <$> WI.asBV byte of
      Just 0 -> pure (Break (acc []))
      Just c -> do
        let c' = toEnum @Word8 (fromInteger c)
        pure (Continue (\l -> acc (c' : l)))
      Nothing -> do
        let msg = "Symbolic value encountered when loading a string"
        liftIO (LCB.addFailedAssertion bak (LCS.Unsupported GHC.callStack msg))

-- | 'ByteChecker' for loading symbolic strings with a concrete null terminator.
--
-- Used in 'loadConcretelyNullTerminatedString'.
concretelyNullTerminatedString ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  ByteChecker m sym bak ([WI.SymBV sym 8] -> [WI.SymBV sym 8]) [WI.SymBV sym 8]
concretelyNullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- liftIO (ptrToBv8 bak bytePtr)
    if isConcreteNullTerminator byte
    then pure (Break (acc []))
    else  pure (Continue (\l -> acc (byte : l)))
  where
    isConcreteNullTerminator symByte =
      case BV.asUnsigned <$> WI.asBV symByte of
        Just 0 -> True
        _ -> False

-- | 'ByteChecker' for loading symbolic strings with a provably-null terminator.
--
-- Used in 'loadSymbolicString'.
provablyNullTerminatedString ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  ByteChecker m sym bak ([WI.SymBV sym 8] -> [WI.SymBV sym 8]) [WI.SymBV sym 8]
provablyNullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> liftIO $ do
    byte <- ptrToBv8 bak bytePtr
    let sym = LCB.backendGetSym bak
    isNullTerm <- isProvablyNullTerminator bak sym byte
    if isNullTerm
    then pure (Break (acc []))
    else  pure (Continue (\l -> acc (byte : l)))

-- Helper, not exported
isProvablyNullTerminator ::
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  bak ->
  sym ->
  WI.SymBV sym 8 ->
  IO Bool
isProvablyNullTerminator bak sym symByte =
  case BV.asUnsigned <$> WI.asBV symByte of
    Just 0 -> pure True
    Just _ -> pure False
    _ ->
      LCBO.withSolverProcess bak (pure False) $ \proc -> do
        z <- WI.bvZero sym (WI.knownNat @8)
        p <- WI.notPred sym =<< WI.bvEq sym z symByte
        WPO.checkSatisfiable proc "isProvablyNullTerminator" p <&>
          \case
            WS.Unsat () -> True
            WS.Sat () -> False
            WS.Unknown -> False

---------------------------------------------------------------------
-- *** For string length

-- | 'ByteChecker' for @strlen@ of concrete strings.
fullyConcreteNullTerminatedStringLength ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  ByteChecker m sym bak Int Int
fullyConcreteNullTerminatedStringLength =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- liftIO (ptrToBv8 bak bytePtr)
    case BV.asUnsigned <$> WI.asBV byte of
      Just 0 -> pure (Break acc)
      Just _ -> pure (Continue $! acc + 1)
      Nothing -> do
        let msg = "Symbolic value encountered when loading a string"
        liftIO (LCB.addFailedAssertion bak (LCS.Unsupported GHC.callStack msg))

-- Helper, not exported
symStringLength ::
  MonadIO m =>
  State.MonadState (WI.Pred sym) m =>
  GHC.HasCallStack =>
  Mem.HasPtrWidth wptr =>
  LCB.IsSymBackend sym bak =>
  -- | How to check if a predicate is false
  (bak -> WI.Pred sym -> m Bool) ->
  ByteChecker m sym bak (WI.SymBV sym wptr) (WI.SymBV sym wptr)
symStringLength predIsFalse =
  ByteChecker $ \bak len bytePtr -> do
    byte <- liftIO (ptrToBv8 bak bytePtr)
    keepGoing <- State.get
    let sym = LCB.backendGetSym bak
    byteWasNonNull <- liftIO (WI.bvIsNonzero sym byte)
    keepGoing' <- liftIO (WI.andPred sym keepGoing byteWasNonNull)
    stopHere <- predIsFalse bak keepGoing'
    if stopHere
    then pure (Break len)
    else do
      State.put keepGoing'
      lenPlusOne <- liftIO (WI.bvAdd sym len =<< WI.bvOne sym ?ptrWidth)
      Continue <$> liftIO (WI.bvIte sym keepGoing' lenPlusOne len)

-- | 'ByteChecker' for @strlen@ of strings with a concrete null terminator.
concretelyNullTerminatedStringLength ::
  MonadIO m =>
  State.MonadState (WI.Pred sym) m =>
  GHC.HasCallStack =>
  Mem.HasPtrWidth wptr =>
  LCB.IsSymBackend sym bak =>
  ByteChecker m sym bak (WI.SymBV sym wptr) (WI.SymBV sym wptr)
concretelyNullTerminatedStringLength =
  symStringLength (\_bak p -> pure (WI.asConstantPred p == Just False))

-- | 'ByteChecker' for @strlen@ for strings with a provably-null terminator.
provablyNullTerminatedStringLength ::
  MonadIO m =>
  State.MonadState (WI.Pred sym) m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  Mem.HasPtrWidth wptr =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  ByteChecker m sym bak (WI.SymBV sym wptr) (WI.SymBV sym wptr)
provablyNullTerminatedStringLength =
  symStringLength $ \bak p ->
    case WI.asConstantPred p of
      Just b -> pure b
      _ ->
        liftIO $ LCBO.withSolverProcess bak (pure False) $ \proc -> do
          WPO.checkSatisfiable proc "provablyNullTerminatedStringLength" p <&>
            \case
              WS.Unsat () -> True
              WS.Sat () -> False
              WS.Unknown -> False

---------------------------------------------------------------------
-- ** 'ByteLoader'

-- | Load a byte from memory.
--
-- The only 'ByteLoader' defined here is 'llvmByteLoader', but Macaw users will
-- most often want one based on @doReadMemModel@.
newtype ByteLoader m sym bak wptr
  = ByteLoader { runByteLoader :: bak -> Mem.LLVMPtr sym wptr -> m (Mem.LLVMPtr sym 8) }

-- | A 'ByteLoader' for LLVM memory based on 'Mem.doLoad'.
llvmByteLoader ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  ) =>
  Mem.MemImpl sym ->
  ByteLoader m sym bak wptr
llvmByteLoader mem =
  ByteLoader $ \bak ptr -> do
    let i1 = Mem.bitvectorType 1
    let p8 = Mem.LLVMPointerRepr (DPN.knownNat @8)
    liftIO (Mem.doLoad bak mem ptr i1 p8 CLD.noAlignment)

---------------------------------------------------------------------
-- * 'loadBytes'

-- | Load a sequence of bytes, one at a time.
--
-- Used to implement 'loadConcretelyNullTerminatedString' and
-- 'loadSymbolicString'. Highly customizable via 'ByteLoader' and 'ByteChecker'.
loadBytes ::
  forall m a b sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Initial accumulator
  a ->
  -- | Pointer to load from
  Mem.LLVMPtr sym wptr ->
  -- | How to load a byte from memory
  ByteLoader m sym bak wptr ->
  -- | How to check if we should continue loading the next byte
  ByteChecker m sym bak a b ->
  m b
loadBytes bak mem = go
 where
  sym = LCB.backendGetSym bak
  go ::
    a ->
    Mem.LLVMPtr sym wptr ->
    ByteLoader m sym bak wptr ->
    ByteChecker m sym bak a b ->
    m b
  go acc ptr loader checker = do
    byte <- runByteLoader loader bak ptr
    runByteChecker checker bak acc byte >>=
      \case
        Break result -> pure result
        Continue acc' -> do
          -- It is important that safety assertions for later loads can use
          -- the assumption that earlier bytes were nonzero, see #1463 or
          -- `crucible-llvm-cli/test-data/T1463-read-bytes.cbl` for details.
          prevByteWasNonNull <-
            liftIO (WI.notPred sym =<< Mem.ptrIsNull sym (WI.knownNat @8) byte)
          loc <- liftIO (WI.getCurrentProgramLoc sym)
          let assump = LCB.BranchCondition loc Nothing prevByteWasNonNull
          liftIO (LCB.addAssumption bak assump)

          ptr' <- liftIO (Mem.doPtrAddOffset bak mem ptr =<< WI.bvOne sym Mem.PtrWidth)
          go acc' ptr' loader checker

---------------------------------------------------------------------
-- * Loading and checking two byte streams

-- ** 'BytesLoader'

-- | Load a byte from each of two memory locations.
--
-- The loader can optionally add assumptions after loading bytes when iteration
-- continues. This is used for null-terminated string operations where we need
-- to assume loaded bytes are non-null.
data BytesLoader m sym bak wptr
  = BytesLoader
      { runBytesLoader :: bak -> Mem.LLVMPtr sym wptr -> Mem.LLVMPtr sym wptr -> m (Mem.LLVMPtr sym 8, Mem.LLVMPtr sym 8)
      -- | Called when the checker returns 'Continue', allowing the loader to
      -- add assumptions about the loaded bytes (e.g., that they are non-null).
      , onContinue :: bak -> Mem.LLVMPtr sym 8 -> Mem.LLVMPtr sym 8 -> m ()
      }

-- | A 'BytesLoader' for LLVM memory based on 'Mem.doLoad'.
--
-- This version does not add any assumptions about loaded bytes.
-- Use this for length-bounded operations like @memcmp@ that need to handle
-- null bytes in the middle of the data.
llvmBytesLoader ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  ) =>
  Mem.MemImpl sym ->
  BytesLoader m sym bak wptr
llvmBytesLoader mem =
  BytesLoader
    { runBytesLoader = \bak ptr1 ptr2 -> do
        let i1 = Mem.bitvectorType 1
        let p8 = Mem.LLVMPointerRepr (DPN.knownNat @8)
        byte1 <- liftIO (Mem.doLoad bak mem ptr1 i1 p8 CLD.noAlignment)
        byte2 <- liftIO (Mem.doLoad bak mem ptr2 i1 p8 CLD.noAlignment)
        pure (byte1, byte2)
    , onContinue = \_ _ _ -> pure ()
    }

-- | A 'BytesLoader' for LLVM memory that adds non-null assumptions.
--
-- This version adds assumptions that loaded bytes are non-null when iteration
-- continues. Use this for null-terminated string operations like @strcmp@.
llvmStringsLoader ::
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  ) =>
  Mem.MemImpl sym ->
  BytesLoader m sym bak wptr
llvmStringsLoader mem =
  BytesLoader
    { runBytesLoader = \bak ptr1 ptr2 -> do
        let i1 = Mem.bitvectorType 1
        let p8 = Mem.LLVMPointerRepr (DPN.knownNat @8)
        byte1 <- liftIO (Mem.doLoad bak mem ptr1 i1 p8 CLD.noAlignment)
        byte2 <- liftIO (Mem.doLoad bak mem ptr2 i1 p8 CLD.noAlignment)
        pure (byte1, byte2)
    , onContinue = \bak byte1 byte2 -> liftIO $ do
        let sym = LCB.backendGetSym bak
        -- Add assumptions that both bytes were nonzero
        prevByte1WasNonNull <- WI.notPred sym =<< Mem.ptrIsNull sym (WI.knownNat @8) byte1
        prevByte2WasNonNull <- WI.notPred sym =<< Mem.ptrIsNull sym (WI.knownNat @8) byte2
        loc <- WI.getCurrentProgramLoc sym
        let assump1 = LCB.BranchCondition loc Nothing prevByte1WasNonNull
        let assump2 = LCB.BranchCondition loc Nothing prevByte2WasNonNull
        LCB.addAssumption bak assump1
        LCB.addAssumption bak assump2
    }

---------------------------------------------------------------------
-- ** 'BytesChecker'

-- | Compute a result from two symbolic bytes, and check if loading should
-- continue to the next pair of bytes.
--
-- Used to compare two byte streams simultaneously, e.g., for 'strcmp'.
newtype BytesChecker m sym bak a b
  = BytesChecker
      { runBytesChecker :: bak -> a -> Mem.LLVMPtr sym 8 -> Mem.LLVMPtr sym 8 -> m (ControlFlow a b) }

-- | 'BytesChecker' for adding a maximum byte length.
withMaxBytes ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  Functor m =>
  -- | Maximum number of bytes to compare
  Integer ->
  -- | What to do when the maximum is reached
  (bak -> a -> m b) ->
  BytesChecker m sym bak a b ->
  BytesChecker m sym bak (a, Integer) b
withMaxBytes limit done checker =
  BytesChecker $ \bak (acc, i) byte1Ptr byte2Ptr ->
    runBytesChecker checker bak acc byte1Ptr byte2Ptr >>=
      \case
        Break r -> pure (Break r)
        Continue r ->
          if i + 1 >= limit
          then Break <$> done bak r
          else pure (Continue (r, i + 1))

-- ** 'loadTwoBytes'

-- | Load sequences of bytes from two pointers simultaneously.
--
-- Used to implement 'strcmp'. Similar to 'loadBytes' but operates on two byte streams.
loadTwoBytes ::
  forall m a b sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  ) =>
  bak ->
  Mem.MemImpl sym ->
  -- | Initial accumulator
  a ->
  -- | First pointer to load from
  Mem.LLVMPtr sym wptr ->
  -- | Second pointer to load from
  Mem.LLVMPtr sym wptr ->
  -- | How to load a byte from each memory location
  BytesLoader m sym bak wptr ->
  -- | How to check if we should continue loading the next bytes
  BytesChecker m sym bak a b ->
  m b
loadTwoBytes bak mem = go
 where
  sym = LCB.backendGetSym bak
  go ::
    a ->
    Mem.LLVMPtr sym wptr ->
    Mem.LLVMPtr sym wptr ->
    BytesLoader m sym bak wptr ->
    BytesChecker m sym bak a b ->
    m b
  go acc ptr1 ptr2 loader checker = do
    (byte1, byte2) <- runBytesLoader loader bak ptr1 ptr2
    runBytesChecker checker bak acc byte1 byte2 >>=
      \case
        Break result -> pure result
        Continue acc' -> do
          -- Let the loader add any assumptions it needs (e.g., non-null for strcmp)
          onContinue loader bak byte1 byte2

          ptr1' <- liftIO (Mem.doPtrAddOffset bak mem ptr1 =<< WI.bvOne sym Mem.PtrWidth)
          ptr2' <- liftIO (Mem.doPtrAddOffset bak mem ptr2 =<< WI.bvOne sym Mem.PtrWidth)
          go acc' ptr1' ptr2' loader checker

---------------------------------------------------------------------
-- ** BytesCheckers for string comparison

-- Helper, not exported
-- Common logic for comparing two bytes after null-terminator checking.
-- Returns Nothing if bytes are equal (should continue), or Just result if different.
compareBytesForStrings ::
  MonadIO m =>
  LCB.IsSymBackend sym bak =>
  bak ->
  WI.SymBV sym 8 ->
  WI.SymBV sym 8 ->
  m (Maybe (WI.SymBV sym 32))
compareBytesForStrings bak byte1 byte2 = do
  let sym = LCB.backendGetSym bak
  let i32 = DPN.knownNat @32
  eq <- liftIO (WI.bvEq sym byte1 byte2)
  case WI.asConstantPred eq of
    Just False -> do
      lt <- liftIO (WI.bvUlt sym byte1 byte2)
      negOne <- liftIO (WI.bvLit sym i32 (BV.mkBV i32 (- 1)))
      one <- liftIO (WI.bvOne sym i32)
      result <- liftIO (WI.bvIte sym lt negOne one)
      pure (Just result)
    _ -> pure Nothing

-- Helper, not exported
-- Common logic for handling null terminator cases in string comparison.
-- Returns Nothing if bytes are equal (should continue), or Just result if different or at null terminator.
handleNullTerminators ::
  MonadIO m =>
  LCB.IsSymBackend sym bak =>
  bak ->
  WI.SymBV sym 32 ->
  Bool ->
  Bool ->
  WI.SymBV sym 8 ->
  WI.SymBV sym 8 ->
  m (Maybe (WI.SymBV sym 32))
handleNullTerminators bak bothNullResult isNull1 isNull2 byte1 byte2 = do
  let sym = LCB.backendGetSym bak
  let i32 = DPN.knownNat @32
  case (isNull1, isNull2) of
    (True, True) -> pure (Just bothNullResult)
    (True, False) -> do
      negOne <- liftIO (WI.bvLit sym i32 (BV.mkBV i32 (- 1)))
      pure (Just negOne)
    (False, True) -> do
      one <- liftIO (WI.bvOne sym i32)
      pure (Just one)
    (False, False) -> compareBytesForStrings bak byte1 byte2

-- | 'BytesChecker' for comparing concrete strings.
--
-- Stops when either string has a concrete null terminator.
fullyConcreteNullTerminatedStrings ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  BytesChecker m sym bak (WI.SymBV sym 32) (WI.SymBV sym 32)
fullyConcreteNullTerminatedStrings =
  BytesChecker $ \bak acc byte1Ptr byte2Ptr -> do
    byte1 <- liftIO (ptrToBv8 bak byte1Ptr)
    byte2 <- liftIO (ptrToBv8 bak byte2Ptr)
    let sym = LCB.backendGetSym bak
    let i32 = DPN.knownNat @32

    case (BV.asUnsigned <$> WI.asBV byte1, BV.asUnsigned <$> WI.asBV byte2) of
      (Just 0, Just 0) -> pure (Break acc)
      (Just 0, Just _) -> do
        negOne <- liftIO (WI.bvLit sym i32 (BV.mkBV i32 (- 1)))
        pure (Break negOne)
      (Just _, Just 0) -> do
        one <- liftIO (WI.bvOne sym i32)
        pure (Break one)
      (Just c1, Just c2) | c1 == c2 -> pure (Continue acc)
      (Just c1, Just c2) -> do
        if c1 < c2
          then do
            negOne <- liftIO (WI.bvLit sym i32 (BV.mkBV i32 (- 1)))
            pure (Break negOne)
          else do
            one <- liftIO (WI.bvOne sym i32)
            pure (Break one)
      _ -> do
        let msg = "Symbolic value encountered when comparing strings"
        liftIO (LCB.addFailedAssertion bak (LCS.Unsupported GHC.callStack msg))

-- | 'BytesChecker' for comparing strings with concrete null terminators.
--
-- Stops when either string has a concrete null terminator.
concretelyNullTerminatedStrings ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  BytesChecker m sym bak (WI.SymBV sym 32) (WI.SymBV sym 32)
concretelyNullTerminatedStrings =
  BytesChecker $ \bak acc byte1Ptr byte2Ptr -> do
    byte1 <- liftIO (ptrToBv8 bak byte1Ptr)
    byte2 <- liftIO (ptrToBv8 bak byte2Ptr)

    let isNull1 = case BV.asUnsigned <$> WI.asBV byte1 of { Just 0 -> True; _ -> False }
    let isNull2 = case BV.asUnsigned <$> WI.asBV byte2 of { Just 0 -> True; _ -> False }

    handleNullTerminators bak acc isNull1 isNull2 byte1 byte2 >>= \case
      Just result -> pure (Break result)
      Nothing -> pure (Continue acc)

-- | 'BytesChecker' for comparing strings with provably null terminators.
--
-- Stops when either string is provably null-terminated.
provablyNullTerminatedStrings ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  BytesChecker m sym bak (WI.SymBV sym 32) (WI.SymBV sym 32)
provablyNullTerminatedStrings =
  BytesChecker $ \bak acc byte1Ptr byte2Ptr -> liftIO $ do
    byte1 <- ptrToBv8 bak byte1Ptr
    byte2 <- ptrToBv8 bak byte2Ptr
    let sym = LCB.backendGetSym bak

    isNull1 <- isProvablyNullTerminator bak sym byte1
    isNull2 <- isProvablyNullTerminator bak sym byte2

    handleNullTerminators bak acc isNull1 isNull2 byte1 byte2 >>= \case
      Just result -> pure (Break result)
      Nothing -> pure (Continue acc)

-- | 'BytesChecker' for comparing strings with concrete null terminators
-- up to a maximum length.
--
-- Combines null-terminator checking (like strcmp) with length bounding
-- (like memcmp). Used for strncmp.
--
-- The accumulator is a pair of the comparison result so far and the current index.
lengthBoundedStringComparison ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  Integer ->
  BytesChecker m sym bak (WI.SymBV sym 32, Integer) (WI.SymBV sym 32)
lengthBoundedStringComparison maxLen =
  let onMaxBytes _bak zero = pure zero
  in withMaxBytes maxLen onMaxBytes concretelyNullTerminatedStrings

-- | 'BytesChecker' for comparing strings with provably null terminators
-- up to a maximum length.
--
-- Combines provably null-terminator checking with length bounding.
--
-- The accumulator is a pair of the comparison result so far and the current index.
lengthBoundedProvablyNullTerminatedStringComparison ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  Integer ->
  BytesChecker m sym bak (WI.SymBV sym 32, Integer) (WI.SymBV sym 32)
lengthBoundedProvablyNullTerminatedStringComparison maxLen =
  let onMaxBytes _bak zero = pure zero
  in withMaxBytes maxLen onMaxBytes provablyNullTerminatedStrings

---------------------------------------------------------------------
-- ** BytesCheckers for length-bounded comparison

-- | 'BytesChecker' for comparing two bytes without length bounds.
--
-- Stops when bytes differ, otherwise continues indefinitely.
simpleByteComparison ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  BytesChecker m sym bak () (WI.SymBV sym 32)
simpleByteComparison =
  BytesChecker $ \bak () byte1Ptr byte2Ptr -> do
    byte1 <- liftIO (ptrToBv8 bak byte1Ptr)
    byte2 <- liftIO (ptrToBv8 bak byte2Ptr)
    compareBytesForStrings bak byte1 byte2 >>= \case
      Just result -> pure (Break result)
      Nothing -> pure (Continue ())

-- | 'BytesChecker' for comparing memory regions with a concrete length bound.
--
-- The accumulator is a pair of unit and the current index. Stops when the index reaches the
-- maximum length, or when bytes differ.
--
-- Returns:
-- * 0 if all bytes up to the length are equal
-- * A negative value if the first differing byte in the first region is less
-- * A positive value if the first differing byte in the first region is greater
lengthBoundedByteComparison ::
  MonadIO m =>
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  -- | Maximum length
  Integer ->
  BytesChecker m sym bak ((), Integer) (WI.SymBV sym 32)
lengthBoundedByteComparison maxLen =
  let onMaxBytes bak () = liftIO (WI.bvZero (LCB.backendGetSym bak) (DPN.knownNat @32))
  in withMaxBytes maxLen onMaxBytes simpleByteComparison
