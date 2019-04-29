

{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM
( LLVM
, registerModuleFn
, llvmGlobals
, register_llvm_overrides
, llvmExtensionImpl
)
where

import           Control.Lens
import           Control.Monad (when)
import           Data.Maybe (isJust)
import qualified Text.LLVM.AST as L

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.CFG.Core (AnyCFG(..), cfgHandle)
import           Lang.Crucible.FunctionHandle (lookupHandleMap, handleName)
import           Lang.Crucible.LLVM.Arch (llvmExtensionEval)
import           Lang.Crucible.LLVM.Extension (LLVM, ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim, bindFnHandle)
import           Lang.Crucible.Utils.MonadVerbosity (showWarning)

registerModuleFn
   :: (L.Symbol, AnyCFG (LLVM arch))
   -> OverrideSim p sym (LLVM arch) rtp l a ()
registerModuleFn (_,AnyCFG cfg) = do
  let h = cfgHandle cfg
      s = UseCFG cfg (postdomInfo cfg)
  binds <- use (stateContext . functionBindings)
  when (isJust $ lookupHandleMap h binds) $
    showWarning ("LLVM function handle registered twice: " ++ show (handleName h))
  bindFnHandle h s

llvmGlobals
   :: LLVMContext arch
   -> MemImpl sym
   -> SymGlobalState sym
llvmGlobals ctx mem = emptyGlobals & insertGlobal var mem
  where var = llvmMemVar $ ctx

llvmExtensionImpl :: HasPtrWidth (ArchWidth arch) => ExtensionImpl p sym (LLVM arch)
llvmExtensionImpl =
  ExtensionImpl
  { extensionEval = llvmExtensionEval
  , extensionExec = llvmStatementExec
  }
