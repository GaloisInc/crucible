# next

* The modified copies of the Rust standard libraries that `mir-json` depends on
  (and `crux-mir` therefore ingests) now live in the `mir-json` repo rather
  than in the `crucible` repo. See the [`mir-json`
  README](https://github.com/GaloisInc/mir-json/blob/master/README.md) for
  details.

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
