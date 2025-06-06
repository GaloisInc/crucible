-- TODO(#1406): Move the definitions of the deprecated imports into this module,
-- and remove the exports from MemModel.
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Manipulating C-style null-terminated strings
module Lang.Crucible.LLVM.MemModel.Strings
  ( Mem.loadString
  , Mem.loadMaybeString
  , Mem.strLen
  , storeString
  ) where

import           Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Data.Parameterized.NatRepr as DPN
import qualified Data.Vector as Vec
import qualified GHC.Stack as GHC
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified What4.Interface as WI
import qualified Lang.Crucible.Simulator as LCS

-- | Whether to stop or keep going
data Continue
  = KeepGoing
  | Stop

-- | Load a sequence of bytes, one at a time.
--
-- Not exported.
loadBytes ::
  forall m a sym bak wptr.
  ( LCB.IsSymBackend sym bak
  , Mem.HasPtrWidth wptr
  , Mem.HasLLVMAnn sym
  , ?memOpts :: Mem.MemOptions
  , GHC.HasCallStack
  , MonadIO m
  , Monoid a
  ) =>
  bak ->
  Mem.MemImpl sym ->
  Mem.LLVMPtr sym wptr ->
  (Mem.LLVMPtr sym 8 -> m (Continue, a)) ->
  m a
loadBytes bak mem = go mempty
 where
  go ::
    a ->
    Mem.LLVMPtr sym wptr ->
    (a -> Mem.LLVMPtr sym 8 -> m (Continue, a)) ->
    m a
  go acc ptr f = do
    let i1 = Mem.bitvectorType 1
    let p8 = Mem.LLVMPointerRepr (DPN.knownNat @8)
    b <- liftIO (Mem.doLoad bak mem ptr i1 p8 CLD.noAlignment)
    -- let err = LCS.AssertFailureSimError "Found pointer instead of byte when loading string" ""
    -- x <- Partial.ptrToBv bak err v
    (continue, result) <- f b
    case continue of
      Stop -> pure result
      KeepGoing ->
        go (result <> acc) _

     -- case BV.asUnsigned <$> asBV x of
     --   Just 0 -> return $ f []
     --   Just c -> do
     --       -- let c' :: Word8 = toEnum $ fromInteger c
     --       p' <- doPtrAddOffset bak mem p =<< bvOne sym PtrWidth
     --       go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
     --   Nothing ->
     --     addFailedAssertion bak
     --        $ Unsupported GHC.callStack "Symbolic value encountered when loading a string"

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
