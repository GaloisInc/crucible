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
                   (lookupHandleMap, SomeHandle(..), mkHandle'
                   , handleArgTypes, handleReturnType
                   )
import           Lang.Crucible.LLVM.Eval (llvmExtensionEval)
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
                   ( llvmStatementExec, HasPtrWidth, HasLLVMAnn, MemOptions, MemImpl
                   , bindLLVMFunPtr, Mem
                   )
import           Lang.Crucible.LLVM.Translation
import           Lang.Crucible.Simulator (FnVal(..), regValue)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim


import           What4.Interface (getCurrentProgramLoc)
import           What4.ProgramLoc (plSourceLoc)
import           What4.FunctionName (functionNameFromText)


-- | Register all the functions defined in the LLVM module.
registerModule ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) ->
   LLVMContext arch ->
   ModuleTranslation arch ->
   OverrideSim p sym LLVM rtp l a ()
registerModule handleWarning llvm_ctx mtrans =
   mapM_ (registerModuleFn handleWarning llvm_ctx mtrans) (map L.decName (mtrans ^. modTransDefs))

-- | Register a specific named function that is defined in the given
--   module translation.
registerModuleFn ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) ->
   LLVMContext arch ->
   ModuleTranslation arch ->
   L.Symbol ->
   OverrideSim p sym LLVM rtp l a SomeHandle
registerModuleFn handleWarning llvm_ctx mtrans sym =
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
      let mvar = llvmMemVar llvm_ctx
      mem <- readGlobal mvar
      mem' <- ovrWithBackend $ \bak ->
                liftIO $ bindLLVMFunPtr bak decl h mem
      writeGlobal mvar mem'

      when (isJust $ lookupHandleMap h $ fnBindings binds) $
        do loc <- liftIO . getCurrentProgramLoc =<< getSymInterface
           liftIO (handleWarning (LLVMTranslationWarning sym (plSourceLoc loc) "LLVM function handle registered twice"))
      liftIO $ mapM_ handleWarning warns
      return (SomeHandle h)

-- | Lazily register all the functions defined in the LLVM module.  See
--   'registerLazyModuleFn' for a description.
registerLazyModule ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) ->
   LLVMContext arch ->
   ModuleTranslation arch ->
   OverrideSim p sym LLVM rtp l a ()
registerLazyModule handleWarning llvm_ctx mtrans =
   mapM_ (registerLazyModuleFn handleWarning llvm_ctx mtrans) (map L.decName (mtrans ^. modTransDefs))

-- | Lazily register the named function that is defnied in the given module
--   translation. This will delay actually translating the function until it
--   is called. This done by first installing a bootstrapping override that
--   will peform the actual translation when first invoked, and then will backpatch
--   its own references to point to the translated function.
registerLazyModuleFn ::
   (1 <= ArchWidth arch, HasPtrWidth (ArchWidth arch), IsSymInterface sym) =>
   (LLVMTranslationWarning -> IO ()) ->
   LLVMContext arch ->
   ModuleTranslation arch ->
   L.Symbol ->
   OverrideSim p sym LLVM rtp l a ()
registerLazyModuleFn handleWarning llvm_ctx mtrans sym =
  case filter (\def -> L.defName def == sym) (L.modDefines (mtrans ^. modTransModule)) of
    [def] ->
      let ?lc = llvm_ctx^.llvmTypeCtx in
      let decl = declareFromDefine def
          (L.Symbol fstr) = L.decName decl
          halloc = mtrans ^. modTransHalloc
       in llvmDeclToFunHandleRepr' decl $ \argTys retTy ->
           do let fn_name = functionNameFromText $ Text.pack (fstr ++ "_bootstrap")
              h <- liftIO $ mkHandle' halloc fn_name argTys retTy

              -- Bind the function handle we just created to the following bootstrapping code,
              -- which actually translates the function on its first execution and patches up
              -- behind itself.
              bindFnHandle h
                $ UseOverride
                $ mkOverride' fn_name retTy
                $ -- This inner action defines what to do when this function is called for the
                  -- first time.  We actually translate the function and install it, which
                  -- overrites the global symbol.
                  do SomeHandle h' <- registerModuleFn handleWarning llvm_ctx mtrans sym
                     case (testEquality argTys (handleArgTypes h'),
                           testEquality retTy (handleReturnType h')) of
                        (Nothing, _) -> panic ("Argument type mismatch when bootstraping function: " ++ fstr)
                                               [ show argTys, show h ]
                        (_, Nothing) -> panic ("Return type mismatch when bootstrapping function: " ++ fstr)
                                               [ show retTy, show h ]
                        (Just Refl, Just Refl) ->
                           do -- Rebind the old handle to call directly into the new handle.
                              -- This makes sure that even if the handle related to the global symbol
                              -- has previously been resolved, the actual code for this function
                              -- is correctly executed.
                              bindFnHandle h
                                $ UseOverride
                                $ mkOverride' fn_name retTy
                                $ (regValue <$> (callFnVal (HandleFnVal h') =<< getOverrideArgs))
                              -- Now, call the new handle
                              regValue <$> (callFnVal (HandleFnVal h') =<< getOverrideArgs)

              -- Bind the bootstrapping function handle to the global symbol
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
