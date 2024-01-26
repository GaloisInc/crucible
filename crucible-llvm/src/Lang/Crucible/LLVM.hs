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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM
  ( LLVM
  , registerModule
  , registerModuleFn
  , registerLazyModule
  , registerLazyModuleFn
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
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.LLVM.Eval (llvmExtensionEval)
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
                   ( llvmStatementExec, HasPtrWidth, HasLLVMAnn, MemOptions, MemImpl
                   , Mem
                   )
import           Lang.Crucible.LLVM.Translation
import           Lang.Crucible.Simulator (regValue, FnVal(..))
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim


import           What4.Interface (getCurrentProgramLoc)
import           What4.ProgramLoc (plSourceLoc)


-- | Register all the functions defined in the LLVM module.
--   This will immediately build Crucible CFGs for each function
--   defined in the module.
registerModule ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) {- ^ A callback for handling traslation warnings -} ->
   ModuleTranslation arch ->
   OverrideSim p sym LLVM rtp l a ()
registerModule handleWarning mtrans =
   mapM_ (registerModuleFn handleWarning mtrans) (map (L.decName.fst) (mtrans ^. modTransDefs))

-- | Register a specific named function that is defined in the given
--   module translation. This will immediately build a Crucible CFG for
--   the named function.
registerModuleFn ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) {- ^ A callback for handling traslation warnings -} ->
   ModuleTranslation arch ->
   L.Symbol ->
   OverrideSim p sym LLVM rtp l a ()
registerModuleFn handleWarning mtrans sym =
  liftIO (getTranslatedCFG mtrans sym) >>= \case
    Nothing ->
      fail $ unlines
        [ "Could not find definition for function"
        , show sym
        ]
    Just (decl, AnyCFG cfg, warns) -> do
      let h = cfgHandle cfg
          s = UseCFG cfg (postdomInfo cfg)
      binds <- use (stateContext . functionBindings)
      let llvmCtx = mtrans ^. transContext
      bind_llvm_handle llvmCtx (L.decName decl) h s

      when (isJust $ lookupHandleMap h $ fnBindings binds) $
        do loc <- liftIO . getCurrentProgramLoc =<< getSymInterface
           liftIO (handleWarning (LLVMTranslationWarning sym (plSourceLoc loc) "LLVM function handle registered twice"))
      liftIO $ mapM_ handleWarning warns

-- | Lazily register all the functions defined in the LLVM module.  See
--   'registerLazyModuleFn' for a description.
registerLazyModule ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) {- ^ A callback for handling traslation warnings -} ->
   ModuleTranslation arch ->
   OverrideSim p sym LLVM rtp l a ()
registerLazyModule handleWarning mtrans =
   mapM_ (registerLazyModuleFn handleWarning mtrans) (map (L.decName.fst) (mtrans ^. modTransDefs))

-- | Lazily register the named function that is defnied in the given module
--   translation. This will delay actually translating the function until it
--   is called. This done by first installing a bootstrapping override that
--   will peform the actual translation when first invoked, and then will backpatch
--   its own references to point to the translated function.
--
--   Note that the callback for printing translation warnings may be called at
--   a much-later point, when the function in question is actually first invoked.
registerLazyModuleFn ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) {- ^ A callback for handling translation warnings -} ->
   ModuleTranslation arch ->
   L.Symbol ->
   OverrideSim p sym LLVM rtp l a ()
registerLazyModuleFn handleWarning mtrans sym =
  liftIO (getTranslatedFnHandle mtrans sym) >>= \case
    Nothing -> 
      fail $ unlines
        [ "Could not find definition for function"
        , show sym
        ]
    Just (decl, SomeHandle h) ->
     do -- Bind the function handle we just created to the following bootstrapping code,
        -- which actually translates the function on its first execution and patches up
        -- behind itself.
        let s =
              UseOverride
              $ mkOverride' (handleName h) (handleReturnType h)
              $ -- This inner action defines what to do when this function is called for the
                -- first time.  We actually translate the function and install it as the
                -- implementation for the function handle, instead of this bootstrapping code.
                liftIO (getTranslatedCFG mtrans sym) >>= \case
                  Nothing ->
                    panic "registerLazyModuleFn"
                      [ "Could not find definition for function in bootstrapping code"
                      , show sym
                      ]
                  Just (_decl, AnyCFG cfg, warns) ->
                    case testEquality (handleType (cfgHandle cfg)) (handleType h) of
                      Nothing -> panic "registerLazyModuleFn"
                                      ["Translated CFG type does not match function handle type",
                                       show (handleType h), show (handleType (cfgHandle cfg)) ]
                      Just Refl ->
                        do liftIO $ mapM_ handleWarning warns
                           -- Here we rebind the function handle to use the translated CFG
                           bindFnHandle h (UseCFG cfg (postdomInfo cfg))
                           -- Now, make recursive call to ourself, which should invoke the
                           -- newly-installed CFG
                           regValue <$> (callFnVal (HandleFnVal h) =<< getOverrideArgs)
   
        -- Bind the function handle to the appropriate global symbol.
        let llvmCtx = mtrans ^. transContext
        bind_llvm_handle llvmCtx (L.decName decl) h s


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
