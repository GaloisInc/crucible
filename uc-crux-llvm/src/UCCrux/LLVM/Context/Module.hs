{-
Module       : UCCrux.LLVM.Context.Module
Description  : LLVM module-level read-only context.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Context.Module
  ( ModuleContext,
    moduleFilePath,
    makeModuleContext,
    llvmModule,
    moduleTranslation,
    dataLayout,
    withTypeContext,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), Simple, Getter, Lens, lens, to)

import           Text.LLVM (Module)

import           Lang.Crucible.LLVM.DataLayout (DataLayout)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext, llvmDataLayout)
{- ORMOLU_ENABLE -}

data ModuleContext arch = ModuleContext
  { _moduleFilePath :: FilePath,
    _llvmModule :: Module,
    _moduleTranslation :: ModuleTranslation arch
  }

moduleFilePath :: Simple Lens (ModuleContext arch) FilePath
moduleFilePath = lens _moduleFilePath (\s v -> s {_moduleFilePath = v})

llvmModule :: Simple Lens (ModuleContext arch) Module
llvmModule = lens _llvmModule (\s v -> s {_llvmModule = v})

moduleTranslation :: Simple Lens (ModuleContext arch) (ModuleTranslation arch)
moduleTranslation = lens _moduleTranslation (\s v -> s {_moduleTranslation = v})

dataLayout :: Getter (ModuleContext arch) DataLayout
dataLayout = moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx . to llvmDataLayout

withTypeContext :: ModuleContext arch -> ((?lc :: TypeContext) => a) -> a
withTypeContext context computation =
  let ?lc = context ^. moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
   in computation

makeModuleContext :: FilePath -> Module -> ModuleTranslation arch -> ModuleContext arch
makeModuleContext = ModuleContext
