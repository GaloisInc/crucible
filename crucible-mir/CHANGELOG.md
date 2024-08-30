# 0.9 -- 2024-08-30

* Implement byte-to-char casts.
* Fix a bug which failed to parse MIR JSON code involving casts from array references to pointers.
* Rearranged handling of constant slices into a reference and a separate static allocation for the body the reference points to.
* Add support for GHC 9.8
* Properly parse ArrayToPointer casts

# 0.3-0.8 -- Skipped to synchronize version numbers.

# 0.2 -- 2024-02-05

* `crucible-mir` now supports the `nightly-2023-01-23` Rust toolchain. Some of
  the highlights of this include:

  * Properly support for Rust's new constant forms
  * Better support for zero-sized constants
  * Encoding enum discriminant types so that `crucible-mir` can know about
    non-`isize` discriminant types (e.g., `Ordering`, which uses an `i8`
    discriminant)
  * A more intelligent way of computing crate disambiguators for looking up
    known types such as `MaybeUninit` and `Option`
* Functions in `Mir.Intrinsics` now avoid taking or returning `SimState` values
  as arguments, instead preferring `SymGlobalState` and `IntrinsicTypes`. This
  makes it possible to call into the `crucible-mir` memory model from SAW
  without needing a full-blown `SimState`, which isn't readily at hand in the
  parts of SAW that need the memory model.
* There are now variants of the memory model–related functions in
  `Mir.Intrinsics` whose names are suffixed with `*IO`. These functions live in
  `IO` instead of `MuxLeafT sym IO`, which make them easier to call from `IO`
  contexts.
* Support enums marked with `repr(transparent)`.
* Fix a bug in which the custom overrides for `rotate_left` and related
  intrinsics were not applied.

# 0.1

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
