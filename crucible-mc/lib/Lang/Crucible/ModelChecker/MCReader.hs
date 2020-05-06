module Lang.Crucible.ModelChecker.MCReader
  ( MCReader (..),
    mcCFG,
    mcGlobInit,
    mcLLVMContext,
  )
where

import qualified Control.Lens as L
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.Globals
import Lang.Crucible.LLVM.Translation

data MCReader arch blocks init ret
  = MCReader
      { _mcCFG :: Core.CFG (LLVM arch) blocks init ret,
        _mcGlobInit :: GlobalInitializerMap,
        _mcLLVMContext :: LLVMContext arch
      }

mcCFG :: L.Lens' (MCReader arch blocks init ret) (Core.CFG (LLVM arch) blocks init ret)
mcCFG = L.lens _mcCFG (\c s -> c {_mcCFG = s})

mcGlobInit :: L.Lens' (MCReader arch blocks init ret) GlobalInitializerMap
mcGlobInit = L.lens _mcGlobInit (\c s -> c {_mcGlobInit = s})

mcLLVMContext :: L.Lens' (MCReader arch blocks init ret) (LLVMContext arch)
mcLLVMContext = L.lens _mcLLVMContext (\c s -> c {_mcLLVMContext = s})
