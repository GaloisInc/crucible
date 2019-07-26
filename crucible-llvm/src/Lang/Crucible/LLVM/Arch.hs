{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.LLVM.Arch
  ( llvmExtensionEval
  ) where

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.Evaluation

import qualified Lang.Crucible.LLVM.Arch.X86 as X86
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel.Pointer

llvmExtensionEval ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  (Int -> String -> IO ()) ->
  EvalAppFunc sym (LLVMExtensionExpr arch)

llvmExtensionEval sym _iTypes _logFn eval e =
  case e of
    X86Expr ex -> X86.eval sym eval ex

    LLVM_PointerExpr _w blk off ->
      do blk' <- eval blk
         off' <- eval off
         return (LLVMPointer blk' off')

    LLVM_PointerBlock _w ptr ->
      llvmPointerBlock <$> eval ptr

    LLVM_PointerOffset _w ptr ->
      llvmPointerOffset <$> eval ptr

    LLVM_PointerIte _w c x y ->
      do cond <- eval c
         LLVMPointer xblk xoff <- eval x
         LLVMPointer yblk yoff <- eval y
         blk <- natIte sym cond xblk yblk
         off <- bvIte sym cond xoff yoff
         return (LLVMPointer blk off)
