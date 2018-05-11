{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.LLVM.Arch
  ( llvmExtensionEval
  ) where

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.Evaluation

import           Lang.Crucible.LLVM.Extension
import qualified Lang.Crucible.LLVM.Arch.X86 as X86

llvmExtensionEval ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  (Int -> String -> IO ()) ->
  EvalAppFunc sym (LLVMExtensionExpr arch)

llvmExtensionEval sym _iTypes _logFn f (X86Expr ex) = X86.eval sym f ex
