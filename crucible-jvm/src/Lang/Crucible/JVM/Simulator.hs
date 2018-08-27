module Lang.Crucible.JVM.Simulator where

import Control.Lens



data CrucibleJavaContext =
  CrucibleJavaContext
  {
    _cjcJVMContext     :: JVMContext
  , _cjcHalloc         :: HandleAllocator RealWorld
  , _cjcCodebase       :: JCB.Codebase
  }

makeLenses ''CrucibleJavaContext
