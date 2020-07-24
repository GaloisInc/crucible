{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Lang.Crucible.LLVM.Arch
  ( llvmExtensionEval
  ) where

import           Control.Monad (forM_)
import qualified Data.List.NonEmpty as NE
import           Data.Parameterized.TraversableF

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError

import qualified Lang.Crucible.LLVM.Arch.X86 as X86
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Partial

-- TODO! This isn't really the right place for this...

assertSideCondition ::
  (HasLLVMAnn sym, IsSymInterface sym) =>
  sym ->
  LLVMSideCondition (RegValue' sym) ->
  IO ()
assertSideCondition sym (LLVMSideCondition (RV p) ub) =
  do p' <- annotateUB sym ub p
     let err = AssertFailureSimError "Undefined behavior encountered" ""
     assert sym p' err

llvmExtensionEval :: forall sym arch.
  (HasLLVMAnn sym, IsSymInterface sym) =>
  sym ->
  IntrinsicTypes sym ->
  (Int -> String -> IO ()) ->
  EvalAppFunc sym (LLVMExtensionExpr arch)

llvmExtensionEval sym _iTypes _logFn eval e =
  case e of
    X86Expr ex -> X86.eval sym eval ex

    LLVM_SideConditions _tp conds val ->
      do conds' <- traverse (traverseF (\x -> RV @sym <$> eval x)) (NE.toList conds)
         forM_ conds' (assertSideCondition sym)
         eval val

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
