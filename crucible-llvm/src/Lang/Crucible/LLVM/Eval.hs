{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Lang.Crucible.LLVM.Eval
  ( llvmExtensionEval
  , callStackFromMemVar
  ) where

import           Control.Lens ((^.), view)
import           Control.Monad (forM_)
import qualified Data.List.NonEmpty as NE
import           Data.Parameterized.TraversableF

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.ExecutionTree (SimState, CrucibleState)
import           Lang.Crucible.Simulator.ExecutionTree (stateGlobals)
import           Lang.Crucible.Simulator.GlobalState (lookupGlobal)
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Types (TypeRepr(..))
import           Lang.Crucible.Panic (panic)

import qualified Lang.Crucible.LLVM.Arch.X86 as X86
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel (memImplHeap)
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack, getCallStack)
import           Lang.Crucible.LLVM.MemModel.MemLog (memState)
import           Lang.Crucible.LLVM.MemModel.Partial
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.Types (Mem)

callStackFromMemVar ::
  SimState p sym ext rtp lang args ->
  GlobalVar Mem ->
  CallStack
callStackFromMemVar state mvar =
  getCallStack . view memState . memImplHeap $
     case lookupGlobal mvar (state ^. stateGlobals) of
       Just v -> v
       Nothing ->
         panic "callStackFromMemVar"
           [ "Global heap value not initialized."
           , "*** Global heap variable: " ++ show mvar
           ]

assertSideCondition ::
  (HasLLVMAnn sym, IsSymBackend sym bak) =>
  bak ->
  CallStack ->
  LLVMSideCondition (RegValue' sym) ->
  IO ()
assertSideCondition bak callStack (LLVMSideCondition (RV p) ub) =
  do let sym = backendGetSym bak
     p' <- annotateUB sym callStack ub p
     let err = AssertFailureSimError "Undefined behavior encountered" (show (UB.explain ub))
     assert bak p' err

llvmExtensionEval ::
  forall sym bak p ext rtp blocks r ctx.
  (HasLLVMAnn sym, IsSymBackend sym bak) =>
  bak ->
  IntrinsicTypes sym ->
  (Int -> String -> IO ()) ->
  CrucibleState p sym ext rtp blocks r ctx ->
  EvalAppFunc sym LLVMExtensionExpr

llvmExtensionEval bak _iTypes _logFn state eval e =
  let sym = backendGetSym bak in
  case e of
    X86Expr ex -> X86.eval sym eval ex

    LLVM_SideConditions mvar _tp conds val ->
      do let callStack = callStackFromMemVar state mvar
         conds' <- traverse (traverseF (\x -> RV @sym <$> eval x)) (NE.toList conds)
         forM_ conds' (assertSideCondition bak callStack)
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

    -- These are not necessarily considered correct, see crucible#366
    LLVM_PoisonBV w -> poisonPanic (BVRepr w)
    LLVM_PoisonFloat fi -> poisonPanic (FloatRepr fi)
  where
    poisonPanic tpr =
      panic
        "llvmExtensionEval"
        [ "Attempting to evaluate poison value"
        , "Type: " ++ show tpr
        ]
