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
