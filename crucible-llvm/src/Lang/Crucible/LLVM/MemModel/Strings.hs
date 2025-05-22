-- TODO(TODO: file an issue, put number here): Move the definitions of the
-- deprecated imports into this module, and remove the exports from MemModel.
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

import qualified Data.Parameterized.NatRepr as DPN
import qualified Data.Vector as Vec
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.LLVM.MemModel as Mem
import qualified What4.Interface as WI

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
