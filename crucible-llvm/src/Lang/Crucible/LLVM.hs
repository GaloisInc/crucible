{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
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
import qualified Text.LLVM.AST as L

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim


registerModuleFn
   :: (L.Symbol, AnyCFG (LLVM arch))
   -> OverrideSim p sym (LLVM arch) rtp l a ()
registerModuleFn (_,AnyCFG cfg) = do
  let h = cfgHandle cfg
      s = UseCFG cfg (postdomInfo cfg)
  stateContext . functionBindings %= insertHandleMap h s


llvmGlobals
   :: LLVMContext arch
   -> MemImpl sym
   -> SymGlobalState sym
llvmGlobals ctx mem = emptyGlobals & insertGlobal var mem
  where var = llvmMemVar $ ctx

llvmExtensionImpl :: HasPtrWidth (ArchWidth arch) => ExtensionImpl p sym (LLVM arch)
llvmExtensionImpl =
  ExtensionImpl
  { extensionEval = \_ _ -> \case
  , extensionExec = llvmStatementExec
  }
