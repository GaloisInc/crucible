# next

# 0.6 -- 2026-01-29

This release supports [version
6](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#6) of
`mir-json`'s schema.

* Support simulating Rust code up to version 1.91.
* Add an intrinsic for [`needs_drop`](https://doc.rust-lang.org/std/intrinsics/fn.needs_drop.html).
* `TyConst` now has a `ConstVal` field to indicate the value of the constant
  used to instantiate a const generic parameter. This has no impact on the
  semantics of `crucible-mir` itself, but this can be used by tools that want
  to distinguish different instantiations of const generic functions.
* Add an intrinsic for [`size_of_val`](https://doc.rust-lang.org/std/intrinsics/fn.size_of_val.html),
  which computes the size of a value in bytes. This works for all sized types
  as well as a limited number of unsized types (currently, only slices).
* Add an intrinsic for [`offset`](https://doc.rust-lang.org/std/intrinsics/fn.offset.html),
  which performs pointer offset arithmetic with bounds checking, mirroring the
  semantics of Rust's `core::intrinsics::offset`.
* Add an intrinsic for [`arith_offset`](https://doc.rust-lang.org/std/intrinsics/fn.arith_offset.html),
  which performs wrapping pointer offset arithmetic (allowing arithmetic beyond
  the end of objects without UB), matching the behavior of Rust's
  `core::intrinsics::arith_offset`.
* Add an intrinsic for [`ptr_offset_from`](https://doc.rust-lang.org/std/intrinsics/fn.ptr_offset_from.html),
  which computes the offset (in elements) between two pointers, mirroring
  Rust's `core::intrinsics::ptr_offset_from`.
* Add an intrinsic for [`ptr_offset_from_unsigned`](https://doc.rust-lang.org/std/intrinsics/fn.ptr_offset_from_unsigned.html),
  which computes the offset (in elements, as an unsigned integer) between two
  pointers.  This intrinsic matches the semantics of Rust's
  core::intrinsics::ptr_offset_from_unsigned, and requires that the first
  pointer is greater than or equal to the second.  If the offset would be
  negative (i.e., the first pointer is less than the second), this is undefined
  behavior.
* Add intrinsics for
  [`cttz`](https://doc.rust-lang.org/std/intrinsics/fn.cttz.html) and
  [`cttz_nonzero`](https://doc.rust-lang.org/std/intrinsics/fn.cttz_nonzero.html),
  which compute the number of trailing zeros in an integer value.
* Replace the `MirVector` type with `MirAggregate`. As part of this change, the
  following have been removed:

  * `MirVectorSymbol`, `MirVectorType`, `MirVectorRepr`, `MirVectorFam`, and
     `MirVector`
  * `Index_RefPath`, `VectorAsMirVector_RefPath`, and `ArrayAsMirVector_RefPath`
     (whose types all depend on MirVector)
  * `MirRef_VectorAsMirVector` and `MirRef_ArrayAsMirVector` (for similar
     reasons)
  * `MirVector_Uninit`, `MirVector_FromVector`, `MirVector_FromArray`, and
    `MirVector_Resize` (for similar reasons)

  Where possible, these should be migrated to corresponding operations on
  `MirAggregate`s. Note that indexing-related operations have been split up
  into three separate operations (`VectorIndex_RefPath`, `ArrayIndex_RefPath`,
  and `AgElem_RefPath`) that work on `Vector`s, `Array`s, and `MirAggregate`s,
  respectively.
* The `()` type, the `!` type, and anonymous function definition types are now
  represented using `MirAggregateType` instead of `UnitType`. As part of this
  change, you may need to change some overrides that implicitly returned `()`
  values to instead return `MirAggregate` values explicitly. The
  `mirAggregate_zst`, `mirAggregate_zstIO`, and `mirAggregate_zstSim` functions
  have been introduced to make this process easier.

# 0.5 -- 2025-11-09

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
* Fix a bug in which static items with non-constant initializer expressions that
  depend on static items with constant initializer expressions would fail to
  simulate correctly.
* Add a new map `layouts` in `Collection` to store layout information of sized
  types as exported by `mir-json`.
* Implement the `size_of` and `(min_)align_of` nullary ops and intrinsics
  correctly using the layout information.
* Support translating `Subslice` projections on slices.
* Add basic scaffolding for representing inline assembly (e.g., using the
  `std::arch::asm!` macro). `crucible-mir` does not support _simulating_ inline
  assembly, but it can now translate code that uses it without crashing.
* Implement basic support for creation and manipulation of union-type values.
* Add an intrinsic for [`exact_div`](https://doc.rust-lang.org/std/intrinsics/fn.exact_div.html),
  which performs integer division that triggers undefined behavior if the
  division has a nonzero remainder. This is implemented for both signed and
  unsigned integers and mirrors the semantics of Rust's
  `core::intrinsics::exact_div`.

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
