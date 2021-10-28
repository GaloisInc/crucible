# next
* `LLVMConfig` now has an `indeterminateLoadBehavior` flag to control the
  `MemOptions` option of the same name. Refer to the `crucible-llvm` changelog
  for more details.
* A `?memOpts :: MemOptions` constraint has been added to
  `Crux.LLVM.Simulate.checkFun`.
