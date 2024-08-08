{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.CLI
  ( withLlvmHooks
  ) where

import Control.Monad.IO.Class (liftIO)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.Simulator.ExecutionTree (ExtensionImpl)
import Lang.Crucible.Simulator.OverrideSim (writeGlobal)

import Lang.Crucible.CLI (SimulateProgramHooks(..), defaultSimulateProgramHooks)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian), defaultDataLayout)
import Lang.Crucible.LLVM.Extension (LLVM, ArchRepr(X86Repr))
import Lang.Crucible.LLVM.MemModel (HasPtrWidth)
import qualified Lang.Crucible.LLVM.MemModel as Mem
import Lang.Crucible.LLVM.Intrinsics (defaultIntrinsicsOptions)
import Lang.Crucible.LLVM.Translation (LLVMContext(..))
import Lang.Crucible.LLVM.TypeContext (mkTypeContext)

import Lang.Crucible.LLVM.Syntax (llvmParserHooks)
import Lang.Crucible.LLVM.Syntax.Overrides (registerLLVMOverrides)
import Lang.Crucible.LLVM.Syntax.TypeAlias (typeAliasParserHooks, x86_64LinuxTypes)

-- | Small helper for providing LLVM language-specific hooks, e.g., for use with
-- 'Lang.Crucible.CLI.execCommand'.
withLlvmHooks ::
  (forall w.
    (HasPtrWidth w, ?parserHooks :: ParserHooks LLVM) =>
    (forall sym. IsSymInterface sym => sym -> ExtensionImpl () sym LLVM) ->
    SimulateProgramHooks LLVM ->
    IO a) ->
  IO a
withLlvmHooks k = do
  ha <- newHandleAllocator
  mvar <- Mem.mkMemVar "llvm_memory" ha
  let ?ptrWidth = knownNat @64
  let ?parserHooks = llvmParserHooks (typeAliasParserHooks x86_64LinuxTypes) mvar
  let simulationHooks =
        defaultSimulateProgramHooks
          { setupHook = \bak _ha -> do
              mem <- liftIO (Mem.emptyMem LittleEndian)
              writeGlobal mvar mem
              let ?recordLLVMAnnotation = \_ _ _ -> pure ()
              let (_errs, tyCtx) =
                    mkTypeContext
                      defaultDataLayout
                      IntMap.empty
                      []
              let llvmCtx =
                    LLVMContext
                    { llvmArch = X86Repr ?ptrWidth
                    , llvmPtrWidth = \kont -> kont ?ptrWidth
                    , llvmMemVar = mvar
                    , _llvmTypeCtx = tyCtx
                    , llvmGlobalAliases = Map.empty
                    , llvmFunctionAliases = Map.empty
                    }
              let ?lc = tyCtx
              let ?memOpts = Mem.defaultMemOptions
              let ?intrinsicsOpts = defaultIntrinsicsOptions
              _ <- registerLLVMOverrides bak llvmCtx
              return ()
          , setupOverridesHook = setupOverrides
          }
  let ext _ = let ?recordLLVMAnnotation = \_ _ _ -> pure ()
              in llvmExtensionImpl Mem.defaultMemOptions
  k ext simulationHooks 