{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.CLI
  ( withLlvmHooks
  ) where

import Control.Monad.IO.Class (liftIO)

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.Simulator.ExecutionTree (ExtensionImpl)
import Lang.Crucible.Simulator.OverrideSim (writeGlobal)

import Lang.Crucible.CLI (SimulateProgramHooks(..), defaultSimulateProgramHooks)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.MemModel (HasPtrWidth, defaultMemOptions, emptyMem, mkMemVar)

import Lang.Crucible.LLVM.Syntax (llvmParserHooks)
import Lang.Crucible.LLVM.Syntax.TypeAlias (typeAliasParserHooks, x86_64LinuxTypes)

withLlvmHooks ::
  (forall w.
    (HasPtrWidth w, ?parserHooks :: ParserHooks LLVM) =>
    (forall sym. IsSymInterface sym => sym -> ExtensionImpl () sym LLVM) ->
    SimulateProgramHooks LLVM ->
    IO a) ->
  IO a
withLlvmHooks k = do
  ha <- newHandleAllocator
  mvar <- mkMemVar "llvm_memory" ha
  let ?ptrWidth = knownNat @64
  let ?parserHooks = llvmParserHooks (typeAliasParserHooks x86_64LinuxTypes) mvar
  let simulationHooks =
        defaultSimulateProgramHooks
          { setupHook = \_sym _ha -> do
              mem <- liftIO (emptyMem LittleEndian)
              writeGlobal mvar mem
          , setupOverridesHook = setupOverrides
          }
  let ext _ = let ?recordLLVMAnnotation = \_ _ _ -> pure ()
              in llvmExtensionImpl defaultMemOptions
  k ext simulationHooks 