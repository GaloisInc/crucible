-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM
  ( LLVM
  , registerModuleFn
  , llvmGlobalsToCtx
  , llvmGlobals
  , register_llvm_overrides
  , llvmExtensionImpl
  ) where

import           Control.Lens
import           Control.Monad (when)
import           Control.Monad.IO.Class
import qualified Text.LLVM.AST as L

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle (lookupHandleMap, handleName)
import           Lang.Crucible.LLVM.Eval (llvmExtensionEval)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
                   ( llvmStatementExec, HasPtrWidth, HasLLVMAnn, MemOptions, MemImpl
                   , bindLLVMFunPtr, Mem
                   )
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Utils.MonadVerbosity (showWarning)


registerModuleFn
   :: (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   LLVMContext arch ->
   (L.Declare, AnyCFG ext) ->
   OverrideSim p sym ext rtp l a ()
registerModuleFn llvm_ctx (decl, AnyCFG cfg) = do
  let h = cfgHandle cfg
      s = UseCFG cfg (postdomInfo cfg)
  binds <- use (stateContext . functionBindings)
  when (isJust $ lookupHandleMap h $ fnBindings binds) $
    showWarning ("LLVM function handle registered twice: " ++ show (handleName h))
  bindFnHandle h s
  let mvar = llvmMemVar llvm_ctx
  sym <- getSymInterface
  mem <- readGlobal mvar
  mem' <- liftIO $ bindLLVMFunPtr sym decl h mem
  writeGlobal mvar mem'


llvmGlobalsToCtx
   :: LLVMContext arch
   -> MemImpl sym
   -> SymGlobalState sym
llvmGlobalsToCtx = llvmGlobals . llvmMemVar

llvmGlobals
   :: GlobalVar Mem
   -> MemImpl sym
   -> SymGlobalState sym
llvmGlobals memVar mem = emptyGlobals & insertGlobal memVar mem

llvmExtensionImpl ::
  (HasLLVMAnn sym) =>
  MemOptions ->
  ExtensionImpl p sym LLVM
llvmExtensionImpl mo =
  let ?memOpts = mo in
  ExtensionImpl
  { extensionEval = llvmExtensionEval
  , extensionExec = llvmStatementExec
  }
