# 0.9 -- 2024-08-30

* Add support for GHC 9.8

# 0.8 -- Skipped to synchronize version numbers.

# 0.7 -- 2024-02-05

* Add a `Crux.Overrides` module, which defines common functionality for defining
  overrides, which are shared among several Crux backends.

# 0.6

* Corresponds to the 0.6 release of `crux-llvm` and `crux-mir`.
* `SimulatorCallbacks` now returns `SimulatorHooks`, a new data type that
  allows hooking into the simulation process at various steps.
