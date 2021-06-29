{-
Module       : UCCrux.LLVM.Overrides.Unsound
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

module UCCrux.LLVM.Overrides.Unsound
  ( UnsoundOverrideName (..),
    unsoundOverrides,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Monad.IO.Class (liftIO)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import           Data.IORef (IORef, modifyIORef)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)

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
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.QQ (llvmOvr)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, Mem, LLVMPointerType)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate(..), basic_llvm_override)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
{- ORMOLU_ENABLE -}

newtype UnsoundOverrideName = UnsoundOverrideName {getUnsoundOverrideName :: Text}
  deriving (Eq, Ord, Show)

------------------------------------------------------------------------

-- ** Declarations

-- | Some additional overrides that are useful for bugfinding, but not for
-- verification. They unsoundly under-approximate the environment. This helps
-- symbolic execution reach more code.
unsoundOverrides ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext
  ) =>
  proxy arch ->
  IORef (Set UnsoundOverrideName) ->
  [OverrideTemplate (personality sym) sym arch rtp l a]
unsoundOverrides arch usedRef =
  [ basic_llvm_override $
      [llvmOvr| i32 @gethostname( i8* , size_t ) |]
        ( \memOps sym args ->
            liftIO (used "gethostname")
              >> Ctx.uncurryAssignment (callGetHostName arch sym memOps) args
        ),
    basic_llvm_override $
      [llvmOvr| i8* @getenv( i8* ) |]
        ( \memOps sym args ->
            liftIO (used "getenv")
              >> Ctx.uncurryAssignment (callGetEnv arch sym memOps) args
        )
  ]
  where
    used :: Text -> IO ()
    used name = modifyIORef usedRef (Set.insert (UnsoundOverrideName name))

------------------------------------------------------------------------

-- ** Implementations

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
    -- NOTE(lb): It isn't currently necessary to check if ?ptrWidth is wide
    -- enough to hold the hostname because the hostname is small and fixed, and
    -- the ArchOk constraint guarantees that the pointer width is at least 16.
    -- if this override is changed to e.g. use really long hostnames it might
    -- be necessary to check that mkBV doesn't truncate the length here.
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

-- | Super unsound. Returns the same string value every time, but in a fresh
-- allocation for each call. A more sound approximation would be to require
-- that the variable name be concrete and then have a map from names to
-- allocations holding values.
callGetEnv ::
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
  OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callGetEnv _proxy sym mvar _ptr =
  do
    let value = "<fake environment variable value>"
    Override.modifyGlobal mvar $ \mem ->
      liftIO $
        do
          let val = LLVMMem.LLVMValString value
          let ty = LLVMMem.llvmValStorableType val
          let lenBv = BV.mkBV ?ptrWidth (fromIntegral $ BS.length value)
          sz <- What4.bvLit sym ?ptrWidth lenBv
          (ptr', mem1) <-
            LLVMMem.doMalloc sym G.GlobalAlloc G.Mutable "getenv" mem sz noAlignment
          mem2 <- LLVMMem.storeRaw sym mem1 ptr' ty noAlignment val
          return (ptr', mem2)
