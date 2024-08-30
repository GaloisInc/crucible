# 0.9 -- 2024-08-30

* Add support for GHC 9.8

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
