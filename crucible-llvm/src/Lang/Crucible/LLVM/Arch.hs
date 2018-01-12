{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.LLVM.Arch
  ( llvmExtensionEval
  ) where

import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Solver.Interface

import           Lang.Crucible.LLVM.Extension
import qualified Lang.Crucible.LLVM.Arch.X86 as X86

llvmExtensionEval ::
  IsSymInterface sym =>
  sym ->
  EvalAppFunc sym (LLVMExtensionExpr arch)

llvmExtensionEval sym f (X86Expr ex) = X86.eval sym f ex
