# next
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `UCCrux.LLVM.Setup`: `generate` and `setupExecution`
  * `UCCrux.LLVM.Setup.Monad`: `malloc`

# 0.2
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `UCCrux.LLVM.Mem`: `store`, `store'`, `storeGlobal`, and `storeGlobal'`
  * `UCCrux.LLVM.Setup.Monad`: `store` and `storeGlobal`
