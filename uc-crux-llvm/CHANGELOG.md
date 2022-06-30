# next
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `UCCrux.LLVM.Setup`: `generate` and `setupExecution`
  * `UCCrux.LLVM.Setup.Monad`: `malloc`

* When loading bitcode to execute, we now make use of a new feature
of `crucible-llvm` which delays the translation of the LLVM bitcode
until functions are actually called. This should speed up startup
times and reduce memory usage for verification tasks where a small
subset of functions in a bitcode module are actually executed.

* The types of `UCCrux.LLVM.Context.Module.findFun` and
  `UCCrux.LLVM.FullType.Translation.translateModuleDefines` have
  changed to accomodate the new lazy-loading feature.


# 0.2
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `UCCrux.LLVM.Mem`: `store`, `store'`, `storeGlobal`, and `storeGlobal'`
  * `UCCrux.LLVM.Setup.Monad`: `store` and `storeGlobal`
