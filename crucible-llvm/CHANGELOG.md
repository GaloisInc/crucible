# next
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `Lang.Crucible.LLVM.MemModel`: `doStore`, `storeRaw`, `condStoreRaw`, and
    `storeConstRaw`
  * `Lang.Crucible.LLVM.Globals`: `populateGlobal`
  * `Lang.Crucible.LLVM.MemModel.Generic`: `writeMem` and `writeConstMem`
* `Lang.Crucible.LLVM`: `registerModuleFn` has changed type to
  accomodate lazy loading of Crucible IR.
* `Lang.Crucible.LLVM.Translation` : The `ModuleTranslation` record is
  now opaque, the `cfgMap` is no longer exported and `globalInitMap`
  and `modTransNonce` have become lens-style getters instead of record
  accessors. CFGs should be retrieved using the new `getTranslatedCFG`
  or `getTranslatedCFGForHandle` functions.
* `Lang.Crucible.LLVM` : new functions `registerLazyModuleFn` and
  `registerLazyModule`, which delay the building of Crucible CFGs until
  the functions in question are actually called.



# 0.4
* A new `indeterminateLoadBehavior` flag in `MemOptions` now controls now
  reading from uninitialized memory works when `laxLoadsAndStores` is enabled.
  If `StableSymbolic` is chosen, then allocating memory will also initialize it
  with a fresh symbolic value so that subsequent reads will always return that
  same value. If `UnstableSymbolic` is chosen, then each read from a section of
  uninitialized memory will return a distinct symbolic value each time.

  As a result of this change, `?memOpts :: MemOptions` constraints have been
  added to the following functions:
  * `Lang.Crucible.LLVM.Globals`:
    `initializeAllMemory`, `initializeMemoryConstGlobals`, `populateGlobals`,
    `populateAllGlobals`, and `populateConstGlobals`
  * `Lang.Crucible.LLVM.MemModel`:
    `doAlloca`, `doCalloc`, `doInvalidate`, `doMalloc`, `doMallocUnbounded`,
    `mallocRaw`, `mallocConstRaw`, `allocGlobals`, and `allocGlobal`
* `HasLLVMAnn` now has an additional `CallStack` argument, which is used for
  annotating errors with call stacks.
