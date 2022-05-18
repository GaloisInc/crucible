# 0.6

## New features

* Improved support for translating LLVM debug metadata when the
  `debug-intrinsics` option is enabled, including metadata that defines
  metadata nodes after they are used.

* Add overrides for certain floating-point operations such as `sin`, `cos`,
  `tan`, etc. At the solver level, `crux-llvm` treats these as uninterpreted
  functions, so `crux-llvm` is limited to reasoning about them up to basic,
  syntactic equivalence checking.

* Certain error messages now print the call stack of functions leading up to
  the error.

## Bug fixes

* Make `--help` and `--version` respect the `--no-colors` flag.

## Library changes

* `LLVMConfig` now has an `indeterminateLoadBehavior` flag to control the
  `MemOptions` option of the same name. Refer to the `crucible-llvm` changelog
  for more details.
* A `?memOpts :: MemOptions` constraint has been added to
  `Crux.LLVM.Simulate.checkFun`.
