{-
Module       : UCCrux.LLVM.Overrides
Description  : Additional overrides
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module UCCrux.LLVM.Overrides
  ( registerUnsoundOverrides,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Control.Monad.IO.Class (liftIO)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (knownNat)

import qualified What4.Interface as What4

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim)
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import           Lang.Crucible.Simulator.RegMap (RegEntry, emptyRegMap, regValue)
import           Lang.Crucible.Simulator.RegValue (RegValue)
import           Lang.Crucible.Types (BVType)

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVM)
import           Lang.Crucible.LLVM.QQ (llvmOvr)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, Mem, LLVMPointerType)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate(..), register_llvm_overrides, basic_llvm_override)

import           Crux.Types (OverM, Model, HasModel)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
{- ORMOLU_ENABLE -}

-- | Register some additional overrides that are useful for bugfinding, but not
-- for verification. They unsoundly under-approximate the environment. This
-- helps symbolic execution reach more code.
registerUnsoundOverrides ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  proxy arch ->
  L.Module ->
  ModuleTranslation arch ->
  OverM Model sym LLVM ()
registerUnsoundOverrides proxy llvmModule mtrans =
  do
    let llvmCtx = mtrans ^. transContext
    let ?lc = llvmCtx ^. llvmTypeCtx
    register_llvm_overrides llvmModule [] (unsoundOverrides proxy) llvmCtx

unsoundOverrides ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    HasModel personality
  ) =>
  proxy arch ->
  [OverrideTemplate (personality sym) sym arch rtp l a]
unsoundOverrides arch =
  [ basic_llvm_override $
      [llvmOvr| i32 @gethostname( i8* , size_t ) |]
        (\memOps sym args -> Ctx.uncurryAssignment (callGetHostName arch sym memOps) args)
  ]

callGetHostName ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    wptr ~ ArchWidth arch,
    ArchOk arch,
    ?lc :: TypeContext
  ) =>
  proxy arch ->
  sym ->
  GlobalVar Mem ->
  RegEntry sym (LLVMPointerType wptr) ->
  RegEntry sym (BVType wptr) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callGetHostName _proxy sym mvar (regValue -> ptr) (regValue -> len) =
  do
    let hostname = "hostname"
    let lenLt bv = liftIO (What4.bvSlt sym len =<< What4.bvLit sym ?ptrWidth bv)
    lenNeg <- lenLt (BV.mkBV ?ptrWidth 0)
    -- TODO(lb): Panic if ?ptrWidth is like 2 or something crazy
    lenSmall <- lenLt (BV.mkBV ?ptrWidth (fromIntegral (BS.length hostname)))
    Override.symbolicBranches
      emptyRegMap
      [ ( lenNeg,
          Override.modifyGlobal mvar $ \_mem ->
            unimplemented "callGetHostName" Unimplemented.GetHostNameNegativeSize,
          Nothing
        ),
        ( lenSmall,
          Override.modifyGlobal mvar $ \_mem ->
            unimplemented "callGetHostName" Unimplemented.GetHostNameSmallSize,
          Nothing
        ),
        -- TODO Check for name size
        -- Otherwise, return a canned name
        ( What4.truePred sym,
          Override.modifyGlobal mvar $ \mem ->
            liftIO $
              do
                let val = LLVMMem.LLVMValString hostname
                let ty = LLVMMem.llvmValStorableType val
                mem1 <- LLVMMem.storeRaw sym mem ptr ty noAlignment val
                bv0' <- What4.bvLit sym (knownNat @32) (BV.mkBV (knownNat @32) 0)
                return (bv0', mem1),
          Nothing
        )
      ]
