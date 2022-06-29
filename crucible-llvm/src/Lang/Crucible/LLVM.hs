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
import qualified Data.Text as Text
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
                   (lookupHandleMap, mkHandle')
import           Lang.Crucible.LLVM.Eval (llvmExtensionEval)
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
                   ( llvmStatementExec, HasPtrWidth, HasLLVMAnn, MemOptions, MemImpl
                   , bindLLVMFunPtr, Mem
                   )
import           Lang.Crucible.LLVM.Translation
import           Lang.Crucible.Simulator (regValue, FnVal(..))
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim


import           What4.Interface (getCurrentProgramLoc)
import           What4.ProgramLoc (plSourceLoc)
import           What4.FunctionName (functionNameFromText)


-- | Register all the functions defined in the LLVM module.
--   This will immediately build Crucible CFGs for each function
--   defined in the module.
registerModule ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) {- ^ A callback for handling traslation warnings -} ->
   ModuleTranslation arch ->
   OverrideSim p sym LLVM rtp l a ()
registerModule handleWarning mtrans =
   mapM_ (registerModuleFn handleWarning mtrans) (map L.decName (mtrans ^. modTransDefs))

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
      bindFnHandle h s
      let llvm_ctx = mtrans ^. transContext
      let mvar = llvmMemVar llvm_ctx
      mem <- readGlobal mvar
      mem' <- ovrWithBackend $ \bak ->
                liftIO $ bindLLVMFunPtr bak decl h mem
      writeGlobal mvar mem'

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
   mapM_ (registerLazyModuleFn handleWarning mtrans) (map L.decName (mtrans ^. modTransDefs))

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
  case filter (\def -> L.defName def == sym) (L.modDefines (mtrans ^. modTransModule)) of
    [def] ->
      let llvm_ctx = mtrans^.transContext in
      let ?lc = llvm_ctx^.llvmTypeCtx in
      let decl = declareFromDefine def
          L.Symbol fstr = L.decName decl
          halloc = mtrans ^. modTransHalloc
       in llvmDeclToFunHandleRepr' decl $ \argTys retTy ->
           do let fn_name = functionNameFromText $ Text.pack fstr
              h <- liftIO $ mkHandle' halloc fn_name argTys retTy

              -- Bind the function handle we just created to the following bootstrapping code,
              -- which actually translates the function on its first execution and patches up
              -- behind itself.
              bindFnHandle h
                $ UseOverride
                $ mkOverride' fn_name retTy
                $ -- This inner action defines what to do when this function is called for the
                  -- first time.  We actually translate the function and install it as the
                  -- implementation for the function handle, instead of this bootstrapping code.
                  liftIO (getTranslatedCFGForHandle mtrans sym h) >>= \case
                    Nothing ->
                      panic "registerLazyModuleFn"
                        [ "Could not find definition for function in bootstrapping code"
                        , show sym
                        ]
                    Just (_decl, SomeCFG cfg, warns) ->
                      do liftIO $ mapM_ handleWarning warns
                         -- Here we rebind the function handle to use the translated CFG
                         bindFnHandle h (UseCFG cfg (postdomInfo cfg))
                         -- Now, make recursive call to ourself, which should invoke the
                         -- newly-installed CFG
                         regValue <$> (callFnVal (HandleFnVal h) =<< getOverrideArgs)

              -- Bind the function handle to the appropriate global symbol.
              let mvar = llvmMemVar llvm_ctx
              mem <- readGlobal mvar
              mem' <- ovrWithBackend $ \bak ->
                        liftIO $ bindLLVMFunPtr bak decl h mem
              writeGlobal mvar mem'

    [] -> fail $ unlines
            [ "Could not find definition for function"
            , show sym
            ]

    ds -> panic ("More than one LLVM definition found for " ++ show (L.ppSymbol sym))
                (map (show . L.ppDeclare . declareFromDefine) ds)


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
