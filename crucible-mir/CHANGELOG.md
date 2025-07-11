# next -- TBA

This release supports [version
2](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#2) of
`mir-json`'s schema.

* Support simulating Rust code up to version 1.86.
* Split out the `StatementKind` and `TerminatorKind` data types from `Statement`
  and `Terminator`, respectively. `{Statement,Terminator}` now contain a pair
  of `{Statement,Terminator}Kind` and its source position.
* Improve source position tracking for `Statement`s and `Terminator`s during
  the translation to Crucible. This should result in more precise error messages
  in certain situations.
* The `CTyBv{128,256,512}` pattern synonyms have been removed. It is not
  expected that there are any downstream users.
* Struct and enum types are now translated directly to `StructType` and
  `RustEnumType` instead of `AnyType`. As a result of these changes,
  `Any_RefPath`, `MirSubanyRef`, `subanyRef`, and similar functions have been
  removed, as they no longer serve a useful purpose.
* Added an intrinsic for [`read_volatile`](https://doc.rust-lang.org/std/ptr/fn.read_volatile.html)
  and [`write_volatile`](https://doc.rust-lang.org/std/ptr/fn.write_volatile.html)
* Support raw-pointer and `CoerceUnsized` casts that introduce vtable metadata.
* Add `Pretty` instances for `Vtable` and `VtableItem`, and make the `Pretty`
  instance for `Collection` print its vtables.
* Generalize the custom overrides for `rotate_{left,right}` to work on integer
  types besides `i32` or `u32`.
* Support clone shims for function pointers and closures.
* Type translation functions like `tyToRepr` now fail gracefully
  so that failed translations can be handled by upstream tooling
  instead of failing using `error`

# 0.4 -- 2025-03-21

This release supports [version
1](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#1) of
`mir-json`'s schema.

* The calling sequence of ```translateMIR``` has changed: the first argument,
  which should always have been passed as ```mempty```, has been removed.
  This will require adjustments in any downstream callers.
* The corresponding implicit argument in the ```Pass``` type has been removed.
* The Semigroup and Monoid instances for Collection, CollectionState, and
  RustModule have been removed. It is not expected that there are any
  downstream users.
* Add a custom override for the
  [`bitreverse`](https://doc.rust-lang.org/std/intrinsics/fn.bitreverse.html)
  intrinsic.

# 0.3 -- 2024-08-30

* Implement byte-to-char casts.
* Fix a bug which failed to parse MIR JSON code involving casts from array references to pointers.
* Rearranged handling of constant slices into a reference and a separate static allocation for the body the reference points to.
* Add support for GHC 9.8
* Properly parse ArrayToPointer casts

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
