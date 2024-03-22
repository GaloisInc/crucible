{-
Module       : UCCrux.LLVM.Overrides.Unsound
Description  : Unsound (indefinite) overrides, possibly helpful for bug-finding
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
{-# LANGUAGE TypeOperators #-}
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
import           Lang.Crucible.Backend (IsSymInterface, backendGetSym)
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim, ovrWithBackend)
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import           Lang.Crucible.Simulator.RegMap (RegEntry, emptyRegMap, regValue)
import           Lang.Crucible.Simulator.RegValue (RegValue)
import           Lang.Crucible.Types (BVType)

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.QQ (llvmOvr)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, Mem, MemOptions, LLVMPointerType)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (basic_llvm_override)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride, ForAllSymArch, makeForAllSymArch)
{- ORMOLU_ENABLE -}

newtype UnsoundOverrideName = UnsoundOverrideName {getUnsoundOverrideName :: Text}
  deriving (Eq, Ord, Show)

------------------------------------------------------------------------

-- ** Declarations

-- | Some additional overrides that are useful for bugfinding, but not for
-- verification. In the sense of @doc/soundness.md@, these overrides are
-- /indefinite/.
unsoundOverrides ::
  (?lc :: TypeContext, ?memOpts :: LLVMMem.MemOptions) =>
  -- | See Note [IORefs].
  IORef (Set UnsoundOverrideName) ->
  [ForAllSymArch PolymorphicLLVMOverride]
unsoundOverrides usedRef =
  [ makeForAllSymArch $
      \arch ->
        makePolymorphicLLVMOverride $
          basic_llvm_override $
            [llvmOvr| i32 @gethostname( i8* , size_t ) |]
              ( \memOps args ->
                  liftIO (used "gethostname")
                    >> Ctx.uncurryAssignment (callGetHostName arch memOps) args
              ),
    makeForAllSymArch $
      \arch ->
        makePolymorphicLLVMOverride $
          basic_llvm_override $
            [llvmOvr| i8* @getenv( i8* ) |]
              ( \memOps args ->
                  liftIO (used "getenv")
                    >> Ctx.uncurryAssignment (callGetEnv arch memOps) args
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
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  proxy arch ->
  GlobalVar Mem ->
  RegEntry sym (LLVMPointerType wptr) ->
  RegEntry sym (BVType wptr) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callGetHostName _proxy mvar (regValue -> ptr) (regValue -> len) =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    let hostname = "hostname"
    let lenLt bv = liftIO (What4.bvSlt sym len =<< What4.bvLit sym ?ptrWidth bv)
    lenNeg <- lenLt (BV.mkBV ?ptrWidth 0)
    -- NOTE(lb): It isn't currently necessary to check if ?ptrWidth is wide
    -- enough to hold the hostname because the hostname is small and fixed, and
    -- the ArchOk constraint guarantees that the pointer width is at least 16.
    -- if this override is changed to e.g. use really long hostnames it might
    -- be necessary to check that mkBV doesn't truncate the length here.
    lenSmall <- lenLt (BV.mkBV ?ptrWidth (toEnum (BS.length hostname)))
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
                mem1 <- LLVMMem.storeRaw bak mem ptr ty noAlignment val
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
    ?lc :: TypeContext,
    ?memOpts :: LLVMMem.MemOptions
  ) =>
  proxy arch ->
  GlobalVar Mem ->
  RegEntry sym (LLVMPointerType wptr) ->
  OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callGetEnv _proxy mvar _ptr =
  ovrWithBackend $ \bak -> do
    let value = "<fake environment variable value>"
    Override.modifyGlobal mvar $ \mem ->
      liftIO $
        do
          let sym = backendGetSym bak
          let val = LLVMMem.LLVMValString value
          let ty = LLVMMem.llvmValStorableType val
          let lenBv = BV.mkBV ?ptrWidth (toEnum (BS.length value))
          sz <- What4.bvLit sym ?ptrWidth lenBv
          (ptr', mem1) <-
            LLVMMem.doMalloc bak G.GlobalAlloc G.Mutable "getenv" mem sz noAlignment
          mem2 <- LLVMMem.storeRaw bak mem1 ptr' ty noAlignment val
          return (ptr', mem2)
