{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.CLI
  ( withLlvmHooks
  ) where

import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Control.Monad.IO.Class (liftIO)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Type.Equality ((:~:)(Refl), testEquality)

import Data.Parameterized.NatRepr (knownNat)
import qualified Data.Parameterized.Map as MapF

import qualified What4.FunctionName as W4

import Lang.Crucible.Backend (IsSymBackend)
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import qualified Lang.Crucible.FunctionHandle as C
import Lang.Crucible.Simulator.ExecutionTree (ExtensionImpl)
import Lang.Crucible.Simulator.OverrideSim (writeGlobal)
import qualified Lang.Crucible.Simulator as C

import Lang.Crucible.CLI (SimulateProgramHooks(..), defaultSimulateProgramHooks)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian), defaultDataLayout)
import Lang.Crucible.LLVM.Extension (LLVM, ArchRepr(X86Repr))
import Lang.Crucible.LLVM.MemModel (HasPtrWidth)
import qualified Lang.Crucible.LLVM.MemModel as Mem
import Lang.Crucible.LLVM.Intrinsics (defaultIntrinsicsOptions, llvmIntrinsicTypes)
import Lang.Crucible.LLVM.SymIO (llvmSymIOIntrinsicTypes)
import Lang.Crucible.LLVM.Translation (LLVMContext(..))
import Lang.Crucible.LLVM.TypeContext (mkTypeContext)

import Lang.Crucible.LLVM.Syntax (llvmParserHooks)
import Lang.Crucible.LLVM.Syntax.Overrides (registerLLVMOverrides)
import qualified Lang.Crucible.LLVM.Syntax.Overrides.String as StrOv
import Lang.Crucible.LLVM.Syntax.TypeAlias (typeAliasParserHooks, x86_64LinuxTypes)

tryBindTypedOverride ::
  C.FnHandle args ret ->
  C.TypedOverride p sym ext args' ret' ->
  C.OverrideSim p sym ext rtp args'' ret'' ()
tryBindTypedOverride hdl ov = do
  let err = fail ("Ill-typed declaration for " ++ Text.unpack (W4.functionName (C.handleName hdl)))
  case testEquality (C.handleArgTypes hdl) (C.typedOverrideArgs ov) of
    Nothing -> err
    Just Refl ->
      case testEquality (C.handleReturnType hdl) (C.typedOverrideRet ov) of
        Nothing -> err
        Just Refl -> C.bindTypedOverride hdl ov

-- | Small helper for providing LLVM language-specific hooks, e.g., for use with
-- 'Lang.Crucible.CLI.execCommand'.
withLlvmHooks ::
  (forall w.
    (HasPtrWidth w, ?parserHooks :: ParserHooks LLVM) =>
    (forall sym bak. IsSymBackend sym bak => bak -> IO (ExtensionImpl () sym LLVM)) ->
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
          { setupHook = \bak _ha fds -> do
              let addIntrinsicTypes types ctx =
                    ctx { C.ctxIntrinsicTypes = MapF.union (C.ctxIntrinsicTypes ctx) types }
              let iTypes = MapF.union llvmIntrinsicTypes llvmSymIOIntrinsicTypes
              C.stateContext Lens.%= addIntrinsicTypes iTypes

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
              Monad.forM_ (Map.toList fds) $ \(nm, C.SomeHandle hdl) -> do
                case nm of
                  "read-bytes" -> tryBindTypedOverride hdl (StrOv.readBytesOverride mvar)
                  "read-c-string" -> tryBindTypedOverride hdl (StrOv.readCStringOverride mvar)
                  "write-bytes" -> tryBindTypedOverride hdl (StrOv.writeBytesOverride mvar)
                  "write-c-string" -> tryBindTypedOverride hdl (StrOv.writeCStringOverride mvar)
                  _ -> pure ()
              return ()
          , setupOverridesHook = setupOverrides
          }
  let ext _ = let ?recordLLVMAnnotation = \_ _ _ -> pure ()
              in pure (llvmExtensionImpl Mem.defaultMemOptions)
  k ext simulationHooks
