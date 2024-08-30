# 0.9 -- 2024-08-30

* Add support for GHC 9.8
* Add integer-related `llvm.vector.reduce.*` intrinsics.
* Add workaround to allow loading bitcode using LLVM's reltable lookup optimization.
* `register_llvm_overrides{,_}` now returns the list of overrides that were
  applied.
* The `doMallocHandle` function was removed.
* The `RegOverrideM` monad was replaced by the `MakeOverride` function newtype.
* Several type parameters were removed from `OverrideTemplate`, and the `ext`
  parameter was added. This had downstream effects in `basic_llvm_override`,
  `polymorphic1_llvm_override`, and other functions for registering overrides.
* Override registration code was generalized. `bind_llvm_{handle,func}`
  now don't require a whole `LLVMContext`, just a `GlobalVar Mem`, and are
  polymorphic over `ext`.
* `build_llvm_override` is now generic over the `ext` type parameter. This
  should be a backwards-compatible change.
* `LLVMOverride` now has an additional `ext` type parameter. See the Haddocks
  for `LLVMOverride` for details and motivation.
* The `llvmOverride_def` field of `LLVMOverride` no longer takes a `bak`
  argument. To retrieve the current symbolic backend, use
  `Lang.Crucible.Simulator.OverrideSim.ovrWithBackend`.
* Add overrides for integer-related `llvm.vector.reduce.*` intrinsics.
* Add support for atomic `fadd`, `fsub`, `fmax`, `fmin`, `uinc_wrap`, and
  `udec_wrap` operations in `atomicrmw` instructions.

# 0.7 - 0.8 -- Skipped to synchronize version numbers.

# 0.6 -- 2024-02-05

* `bindLLVMFunPtr` now accepts an `Text.LLVM.AST.Symbol` rather than a whole `Declare`.
  Use `decName` to get a `Symbol` from a `Declare`.
* Implement overrides for the LLVM `llvm.is.fpclass.f*` intrinsics.
* Implement overrides for the `isinf`, `__isinf`, and `__isinff` C functions.
* Implement overrides for the LLVM `llvm.fma.f*` and `llvm.fmuladd.f*`
  intrinsics.
* Implement overrides for the `fma` and `fmaf` C functions.
* Add a `Lang.Crucible.LLVM.MemModel.CallStack.null` function.
* Add a `ppLLVMLatest` function to `Lang.Crucible.LLVM.PrettyPrint`, which
  pretty-prints an LLVM AST using the latest LLVM version that `llvm-pretty`
  currently supports. Also add derived combinators (`ppDeclare`, `ppIdent`,
  etc.) for calling the `llvm-pretty` functions of the same names in tandem
  with `ppLLVMLatest`.

# 0.5
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
* `executeDirectives` in `Lang.Crucible.LLVM.Printf` now returns a `ByteString`
  instead of a `String` so that we can better preserve the exact bytes used in
  string arguments, without applying a particular text encoding.
* `crucible-llvm` now handles LLVM's opaque pointer types, an alternative
  representation of pointer types that does not store a pointee type. As a
  result, `MemType` now has an additional `PtrOpaqueType` constructor in
  addition to the existing (non-opaque) `PtrType` constructor.

  LLVM 15 and later use opaque pointers by default, so it is recommended that
  you add support for `PtrOpaqueType` (and opaque pointers in general) going
  forward. `crucible-llvm` still supports both kinds of pointers, so you can
  fall back to non-opaque pointers if need be.
* A new `Lang.Crucible.LLVM.SimpleLoopInvariant` module has been added, which
  provides an execution feature that facilitates reasoning about certain kinds
  of loops (which may not terminate) using loop invariants. Note that this
  functionality is very experimental and subject to change in the future.

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
