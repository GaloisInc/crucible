# next

This release supports [version
9](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#9) of
`mir-json`'s schema.

# 0.12 -- 2026-01-29

This release supports [version
8](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#8) of
`mir-json`'s schema.

* Support simulating Rust code up to version 1.91.
* Counterexample models are now pretty-printed instead of emitted as JSON.
* Align the Rust language edition used by the test suite’s `rustc` invocation
  with `mir-json` (now defaults to Rust 2021), enabling tests that rely on
  post-2015 language features.
* Add a `--mir-json-arg` option for passing extra arguments to `mir-json`.
* Support using `async fn` and `#[coroutine]`.

# 0.11 -- 2025-11-09

This release supports [version
3](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#3) of
`mir-json`'s schema.

* Additional overrides by the simulator may maintain an external state
* Support simulating Rust code up to version 1.86.
* The modified copies of the Rust standard libraries that `mir-json` depends on
  (and `crux-mir` therefore ingests) now live in the `mir-json` repo rather
  than in the `crucible` repo. See the [`mir-json`
  README](https://github.com/GaloisInc/mir-json/blob/master/README.md) for
  details.
* Improve source position tracking for MIR statements during the translation to
  Crucible. This should result in more precise error messages in certain
  situations.
* Support using `dyn Fn` and `dyn FnMut` for closures.  Using `dyn FnOnce` is
  not yet supported.
* Support custom dynamically-sized types, allowing for use of types like
  `Arc<dyn Fn>`, `Box<dyn Fn>`, et al.
* Fix a bug where concretizing reference values or `Vec` values would cause the
  simulator to crash when attempting to read from the concretized values.
* Add a `--test-skip-filter <string>` flag, which only runs tests whose names
  do not contain `<string>`. This acts as a `crux-mir` analog to `cargo test`'s
  `--skip` flag.
* Fix a bug that could cause the `crucible::concretize` function to crash Crux
  when using the `bitwuzla`, `cvc4`, or `cvc5` solvers.
* Allow calling `crucible::concretize` on `static` references.
* Allow casting pointers to unsafe pointers, which at present should be OK,
  as we don't track the safe/unsafe attribute of pointers anyway.

# 0.10 -- 2025-03-21

This release supports [version
1](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#1) of
`mir-json`'s schema.

* Add a `_version` field to `Collection`, which represents the `mir-json` schema
  version of the MIR JSON file.
* Explicitly check that the `mir-json` schema version is supported when parsing
  a MIR JSON file. If the version is not supported, it will be rejected. This
  helps ensure that unsupported `mir-json` files do not cause unintended
  results.
* Add `--debug` option for starting the Crucible debugger.
* The test suite is now called `crux-mir-test` instead of just `test`.

# 0.9 -- 2024-08-30

* Add support for GHC 9.8
* Constant slice updates in accordance with downstream changes from `crucible-mir`.

# 0.8 -- 2024-02-05

* `crux-mir` now supports the `nightly-2023-01-23` Rust toolchain. Some of the
   highlights of this include:

  * Properly support for Rust's new constant forms
  * Better support for zero-sized constants
  * Encoding enum discriminant types so that `crux-mir` can know about
    non-`isize` discriminant types (e.g., `Ordering`, which uses an `i8`
    discriminant)
  * A more intelligent way of computing crate disambiguators for looking up
    known types such as `MaybeUninit` and `Option`
* Support code that uses `vec::IntoIter` on length-0 `Vec` values.

# 0.7 -- 2023-06-26

## API changes

* Much of the `crux-mir` library has been split off into a `crucible-mir`
  library, which removes all of the `crux`-specific code. The following modules
  were _not_ migrated to `crucible-mir`:

  * `Mir.Generate`
  * `Mir.Language`
  * `Mir.Log`
  * `Mir.Concurrency`
  * `Mir.Overrides`

  Note that `Mir.Generate` now only exports the `generateMIR` function. The
  `parseMIR` and `translateMIR` functions have been moved to a new
  `Mir.ParseTranslate` module in `crucible-mir`.

# 0.6

## Bug fixes

* `Any`-typed local variables are no longer initialized to a default value,
  which prevents spurious assertion failures if these variables become involved
  in symbolic branches in certain cases.
