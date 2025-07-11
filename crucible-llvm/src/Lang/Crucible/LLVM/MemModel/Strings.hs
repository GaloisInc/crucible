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
  ( Mem.loadString
  , Mem.loadMaybeString
  , Mem.strLen
  , loadConcretelyNullTerminatedString
  , loadProvablyNullTerminatedString
  , storeString
  -- * Low-level string loading primitives
  -- ** 'ByteChecker'
  , ControlFlow(..)
  , ByteChecker(..)
  , withMaxChars
  -- ** 'ByteChecker'
  , fullyConcreteNullTerminatedString
  , concretelyNullTerminatedString
  , provablyNullTerminatedString
  -- ** 'ByteLoader'
  , ByteLoader(..)
  , llvmByteLoader
  -- ** 'loadBytes'
  , loadBytes
  ) where

import           Data.Bifunctor (Bifunctor(bimap, first))
import           Control.Monad.IO.Class (MonadIO, liftIO)
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
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.SatResult as WS

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
  zeroNat <- WI.natLit sym 0
  let bytes = Vec.map (Mem.LLVMValInt zeroNat) bytesBvs
  zeroByte <- Mem.LLVMValInt zeroNat <$> WI.bvZero sym (DPN.knownNat @8)
  let nullTerminatedBytes = Vec.snoc bytes zeroByte
  let val = Mem.LLVMValArray (Mem.bitvectorType 1) nullTerminatedBytes
  let storTy = Mem.llvmValStorableType @sym val
  Mem.storeRaw bak mem ptr storTy CLD.noAlignment val

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
    if i > limit
    then Break <$> done acc
    else first (, i + 1) <$> runByteChecker checker bak acc bytePtr

---------------------------------------------------------------------
-- ** For loading strings

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
  ByteChecker $ \bak acc bytePtr -> do
    byte <- liftIO (ptrToBv8 bak bytePtr)
    let sym = LCB.backendGetSym bak
    isNullTerm <- liftIO (isNullTerminator bak sym byte)
    if isNullTerm
    then pure (Break (acc []))
    else  pure (Continue (\l -> acc (byte : l)))
  where
    isNullTerminator bak sym symByte =
      case BV.asUnsigned <$> WI.asBV symByte of
        Just 0 -> pure True
        Just _ -> pure False
        _ ->
          LCBO.withSolverProcess bak (pure False) $ \proc -> do
            z <- WI.bvZero sym (WI.knownNat @8)
            p <- WI.notPred sym =<< WI.bvEq sym z symByte
            WPO.checkSatisfiable proc "provablyNullTerminatedString" p <&>
              \case
                WS.Unsat () -> True
                WS.Sat () -> False
                WS.Unknown -> False

---------------------------------------------------------------------
-- ** For string length

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
