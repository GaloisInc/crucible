# next

* The `LLVM_Debug` data constructor for `LLVMStmt`, as well as the related
  `LLVM_Dbg` data type, have been removed.
* Remove `aggInfo` in favor of `aggregateAlignment`, a lens that retrieves an
  `Alignment` instead of a full `AlignInfo`. In practice, `aggInfo` would only
  ever contain a single size (`0`) in its `AlignInfo`, and the concept of
  "size" doesn't really apply to aggregate alignments in data layout strings,
  so this was simplified to just be an `Alignment` instead.
* Support simulating bitcode that uses features from LLVM 19, including
  [debug records](https://llvm.org/docs/RemoveDIsDebugInfo.html) and
  [`getelementptr`
  attributes](https://releases.llvm.org/19.1.0/docs/LangRef.html#id237).
* Support the `nneg` flag in `zext` and `uitofp` instructions. If `nneg` is
  set, then converting a negative argument will yield a poisoned result.
* Support the `nuw` and `nsw` flags in `trunc` instructions. If `nuw` or `nsw`
  is set, then performing a truncation that would result in unsigned or signed
  integer overflow, respectively, will yield a poisoned result.
* Support the `samesign` flag in `icmp` instructions. If `samesign` is set, then
  comparing two integers of different signs will yield a poisoned result.
* Support the `llvm.tan`, `llvm.a{sin,cos,tan}`, `llvm.{sin,cos,tan}h`, and
  `llvm.atan2` floating-point intrinsics.
* Add extremely limited support for representing `poison` constants. For more
  details on the extent to which `crucible-llvm` can reason about `poison`, see
  `doc/limitations.md`.

  As part of these changes:

  * `LLVMVal` now features an additional `LLVMValPoison` data constructor.
  * `LLVMExpr` now features an additional `PoisonExpr` data constructor.
  * `LLVMConst` now features an addition `PoisonConst` data constructor.
  * `LLVMExtensionExpr` now features `LLVM_Poison{BV,Float}` data constructors,
    which represent primitive `poison` values.
* Remove the `Eq LLVMConst` instance. This instance was inherently unreliable
  because it cannot easily compute a simple `True`-or-`False` answer in the
  presence of `undef` or `poison` values.
* Replace `Data.Dynamic.Dynamic` with `SomeFnHandle` in
  `MemModel.{doInstallHandle,doLookupHandle}`.
* Add pretty-printing functions for use with `Lang.Crucible.Types.ppTypeRepr`
  * `Lang.Crucible.LLVM.MemModel.ppLLVMIntrinsicTypes`
  * `Lang.Crucible.LLVM.MemModel.ppLLVMMemIntrinsicType`
  * `Lang.Crucible.LLVM.MemModel.Pointer.ppLLVMPointerIntrinsicType`
* Overrides for `strnlen`, `strcpy`, `strdup`, and `strndup` supported by new
  APIs in `Lang.Crucible.LLVM.MemModel.Strings`.

# 0.8.0 -- 2025-11-09

* `Lang.Crucible.LLVM.MemModel.{loadString,loadMaybeString,strLen}`
  should now be imported from `Lang.Crucible.LLVM.MemModel.Strings`.
* Two new functions for loading C-style null-terminated strings from
  LLVM memory were added to `Lang.Crucible.LLVM.MemModel.Strings`:
  `loadConcretelyNullTerminatedString` and `loadProvablyNullTerminatedString`.
* Add a new "low-level" API for loading strings to
  `Lang.Crucible.LLVM.MemModel.Strings`: `ByteLoader`, `ByteChecker`, and
  `loadBytes`.
* Support simulating LLVM bitcode files whose data layout strings specify
  function pointer alignment.
* Fix a bug that would cause the simuator to compute incorrect results for the
  `llvm.is.fpclass` intrinsic. (Among other things, this is used to power the
  `isnan` function in Clang 17 or later.)
* Support vectorized versions of the `llvm.u{min,max}` and `llvm.s{min,max}`
  intrinsics.

# 0.7.1 -- 2025-03-21

* Fix a bug in which the memory model would panic when attempting to unpack
  constant string literals.

# 0.7 -- 2024-08-30

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
  accommodate lazy loading of Crucible IR.
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
