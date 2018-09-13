module Lang.Crucible.JVM.Simulator where

import Lang.Crucible.JVM.Translation

import Control.Lens

data CrucibleJavaContext =
  CrucibleJavaContext
  {
    _cjcSim            :: sym
  ,  _cjcPersonality    :: p
  ,  _cjcVerbosity      :: Verbosity
  ,  _cjcJVMContext     :: JVMContext
  , _cjcHalloc         :: HandleAllocator RealWorld
  , _cjcCodebase       :: JCB.Codebase
  }

makeLenses ''CrucibleJavaContext
