# next

# 0.8 -- 2025-11-09

* We now support running simulations with custom users state.
  For this reason, some of the Crux types now have an additional `st`
  parameter.

* `showBVLiteral` has been renamed to `showBVLiteralSigned` and
  two additional functions `showBVLiteralUnsigned` and `showBVLiteralDecimal`
  were added to improve printing of bit vectors

# 0.7.2 -- 2025-03-21

* Add support for the Bitwuzla SMT solver.
* Add `--debug` option for starting the Crucible debugger.
* For the sake of the `--debug` flag, Crux now depends on the
  `crucible-{debug,syntax}` packages.

# 0.7.1 -- 2024-08-30

* Add support for GHC 9.8

# 0.7 -- 2024-02-05

* Add a `Crux.Overrides` module, which defines common functionality for defining
  overrides, which are shared among several Crux backends.

# 0.6

* Corresponds to the 0.6 release of `crux-llvm` and `crux-mir`.
* `SimulatorCallbacks` now returns `SimulatorHooks`, a new data type that
  allows hooking into the simulation process at various steps.
