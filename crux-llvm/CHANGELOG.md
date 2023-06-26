# 0.7 -- 2023-06-26

## New features

* When loading bitcode to execute, we now make use of a new feature
of `crucible-llvm` which delays the translation of the LLVM bitcode
until functions are actually called. This should speed up startup
times and reduce memory usage for verification tasks where a small
subset of functions in a bitcode module are actually executed.

* Added support for the `cvc5` SMT solver.

* Added support for getting abducts during online goal solving. With
the `--get-abducts n` option, `crux-llvm` returns `n` abducts for
each goal that the SMT solver found to be `sat`. An abduct is a formula
that makes the goal `unsat` (would help the SMT solver prove the goal).
This feature only works with the `cvc5` SMT solver.

* Support LLVM versions up to 16.

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
