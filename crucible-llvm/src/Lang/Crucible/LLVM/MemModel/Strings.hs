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
  , loadSymbolicString
  , storeString
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
-- * Check if the byte is concretely a null terminator
--   ('concretelyNullTerminatedString')
-- * Check if a byte is known by a solver to be a null terminator ('nullTerminatedString')
-- * Check if we have surpassed a length limit ('withMaxChars')
--
-- Note that it is relatively common for @a@ to be a function @[b] -> [b]@. This
-- is used to build up a snoc-list.
newtype ByteChecker m sym bak a b
  = ByteChecker { runByteChecker :: bak -> a -> Mem.LLVMPtr sym 8 -> m (ControlFlow a b) }

-- | Load a sequence of bytes, one at a time.
--
-- Not exported.
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
  Mem.LLVMPtr sym wptr ->
  ByteChecker m sym bak a b ->
  m b
loadBytes bak mem = go
 where
  sym = LCB.backendGetSym bak
  go ::
    a ->
    Mem.LLVMPtr sym wptr ->
    ByteChecker m sym bak a b ->
    m b
  go acc ptr f = do
    let i1 = Mem.bitvectorType 1
    let p8 = Mem.LLVMPointerRepr (DPN.knownNat @8)
    byte <- liftIO (Mem.doLoad bak mem ptr i1 p8 CLD.noAlignment)
    runByteChecker f bak acc byte >>=
      \case
        Break result -> pure result
        Continue acc' -> do
          ptr' <- liftIO (Mem.doPtrAddOffset bak mem ptr =<< WI.bvOne sym Mem.PtrWidth)
          go acc' ptr' f

ptrToBv8 ::
  LCB.IsSymBackend sym bak =>
  bak ->
  Mem.LLVMPtr sym 8 ->
  IO (WI.SymBV sym 8)
ptrToBv8 bak bytePtr = do
  let err = LCS.AssertFailureSimError "Found pointer instead of byte when loading string" ""
  Partial.ptrToBv bak err bytePtr

-- Currently unused, but analogous with
-- 'Lang.Crucible.LLVM.MemModel.loadString'. In fact, it would be good to define
-- that function in terms of this one. However, this is blocked on TODO(#1406).
_fullyConcreteNullTerminatedString ::
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  ByteChecker IO sym bak ([Word8] -> [Word8]) [Word8]
_fullyConcreteNullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- ptrToBv8 bak bytePtr
    case BV.asUnsigned <$> WI.asBV byte of
      Just 0 -> pure (Break (acc []))
      Just c -> do
        let c' = toEnum @Word8 (fromInteger c)
        pure (Continue (\l -> acc (c' : l)))
      Nothing -> do
        let msg = "Symbolic value encountered when loading a string"
        LCB.addFailedAssertion bak (LCS.Unsupported GHC.callStack msg)

-- | Helper for loading symbolic strings with a concrete null terminator
concretelyNullTerminatedString ::
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  ByteChecker IO sym bak ([WI.SymBV sym 8] -> [WI.SymBV sym 8]) [WI.SymBV sym 8]
concretelyNullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- ptrToBv8 bak bytePtr
    if isConcreteNullTerminator byte
    then pure (Break (acc []))
    else  pure (Continue (\l -> acc (byte : l)))
  where
    isConcreteNullTerminator symByte =
      case BV.asUnsigned <$> WI.asBV symByte of
        Just 0 -> True
        _ -> False

-- | Helper for loading symbolic strings with a null terminator
nullTerminatedString ::
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  sym ~ WEB.ExprBuilder scope st fs =>
  bak ~ LCBO.OnlineBackend solver scope st fs =>
  WPO.OnlineSolver solver =>
  ByteChecker IO sym bak ([WI.SymBV sym 8] -> [WI.SymBV sym 8]) [WI.SymBV sym 8]
nullTerminatedString =
  ByteChecker $ \bak acc bytePtr -> do
    byte <- ptrToBv8 bak bytePtr
    let sym = LCB.backendGetSym bak
    isNullTerm <- isNullTerminator bak sym byte
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
            WPO.checkSatisfiable proc "nullTerminatedString" p <&>
              \case
                WS.Unsat () -> True
                WS.Sat () -> False
                WS.Unknown -> False

withMaxChars ::
  GHC.HasCallStack =>
  LCB.IsSymBackend sym bak =>
  Functor m =>
  Int ->
  (a -> m b) ->
  ByteChecker m sym bak a b ->
  ByteChecker m sym bak (a, Int) b
withMaxChars limit done checker =
  ByteChecker $ \bak (acc, i) bytePtr ->
    if i > limit
    then Break <$> done acc
    else first (, i + 1) <$> runByteChecker checker bak acc bytePtr

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
  case limit of
    Nothing -> loadBytes bak mem id ptr concretelyNullTerminatedString
    Just l ->
      let byteChecker = withMaxChars l (\f -> pure (f [])) concretelyNullTerminatedString in
      loadBytes bak mem (id, 0) ptr byteChecker

-- | Load a null-terminated string from memory.
--
-- Consults an SMT solver to check if any of the loaded bytes are known to be
-- null (0). If a maximum number of characters is provided, no more than that
-- number of charcters will be read. In either case, 'loadSymbolicString' will
-- stop reading if it encounters a null terminator.
--
-- Note that the loaded string may actually be smaller than the returned list if
-- any of the symbolic bytes are equal to 0.
loadSymbolicString ::
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
loadSymbolicString bak mem ptr limit =
  case limit of
    Nothing -> loadBytes bak mem id ptr nullTerminatedString
    Just l ->
      let byteChecker = withMaxChars l (pure . ($ [])) nullTerminatedString in
      loadBytes bak mem (id, 0) ptr byteChecker

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
