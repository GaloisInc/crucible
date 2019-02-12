-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Types
-- Description      : Types used in override definitions
-- Copyright        : (c) Galois, Inc 2015-2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.LLVM.Intrinsics.Types
  ( LLVMOverride(..)
  , SomeLLVMOverride(..)
  , llvmSizeT
  ) where

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel

-- | This type represents an implementation of an LLVM intrinsic function in
-- Crucible.
data LLVMOverride p sym arch args ret =
  LLVMOverride
  { llvmOverride_declare :: L.Declare    -- ^ An LLVM name and signature for this intrinsic
  , llvmOverride_args    :: CtxRepr args -- ^ A representation of the argument types
  , llvmOverride_ret     :: TypeRepr ret -- ^ A representation of the return type
  , llvmOverride_def ::
       forall rtp args' ret'.
         GlobalVar Mem ->
         sym ->
         Ctx.Assignment (RegEntry sym) args ->
         OverrideSim p sym (LLVM arch) rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

data SomeLLVMOverride p sym arch =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym arch args ret)

-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth
