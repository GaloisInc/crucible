# 0.2.1 -- 2025-11-09

* Store debugger state in the Crucible personality.

# 0.2
* `crucible-wasm` now fully supports functions that return multiple results,
  as described in
  [this WebAssembly proposal](https://github.com/WebAssembly/spec/pull/1145).
* `crucible-wasm` now supports Wasm's `extend_N_S` operations, as described in
  [this WebAssembly proposal](https://github.com/WebAssembly/spec/pull/1144).
* `crucible-wasm` now parses `.wat` files (for textual syntax), `.wast` files
  (for script syntax), and `.wasm` files (for binary files) using different
  parsers. (Previously, `crucible-wasm` assumed that any input files should be
  parsed as script syntax.)
* Add `?memOpts :: MemOptions` constraints to the following functions:
  * `Lang.Crucible.Wasm`: `execScript`
  * `Lang.Crucible.Wasm.Memory`: `wasmStoreChunk`, `wasmStoreInt`,
    `wasmStoreFloat`, and `wasmStoreDouble`
