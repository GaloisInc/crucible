# Patching the Rust standard library

This directory bundles a copy of the Rust standard library with various patches
applied in certain key places to make the resulting code easier for Crucible to
handle. These patches must be applied every time that the bundled Rust standard
library is updated. Moreover, this code often looks quite different each time
between Rust versions, so applying the patches is rarely as straightforward as
running `git apply`.

As a compromise, this document contains high-level descriptions of each type of
patch that we apply, along with rationale for why the patch is necessary. The
intent is that this document can be used in conjunction with `git blame` to
identify all of the code that was changed in each patch.

* Use Crucible's allocator in `alloc/src/raw_vec.rs` (last applied: April 14, 2023)

  The `Allocator` for `RawVec`s is quite involved and is beyond Crucible's
  ability to reason about. We replace the `Allocator` with the corresponding
  built-in Crucible allocation functions (e.g., `crucible::alloc::allocate`).
  We also make sure to avoid the `Layout::array` function, which has a
  particularly tricky use of `transmute` that we do not currently support.

* Use crucible's allocator instead of `rustc_box` (last applied: May 17, 2023)

  Same reasoning as above.

* Reimplement `core::fmt` using `crucible::any::Any` (last applied: May 2, 2023)

  TODO: Describe why this is necessary

* Implement `HashMap` in terms of `Vec` (last applied: May 4, 2023)

  TODO: Describe why this is necessary

* Implement `ptr::invalid` and `ptr::invalid_mut` in terms of casts instead of
  `transmute` (last applied: May 9, 2023)

  The uses of `transmute` in these two functions are particularly nasty, so we
  choose a simpler implementation in terms of casts instead. These uses of
  `transmute` are meant to support strict provenance for Rust pointers, but we
  ignore this in `crucible-mir`.

* Avoid pointer arithmetic in slice iterators (last applied: May 9, 2023)

  Upstream slice::Iter has `ptr` and `end` fields, and computes the length
  by subtracting the two.  This is difficult for us to support at the
  moment.  We can compute the difference between two pointers into the
  same array, but we don't have a good way to decide whether two
  `Const_RefRoot`s are "the same object" or not.  (We could assign them a
  `Nonce` for identity, but since the point of `Const_RefRoot` is to
  support muxing, we'd have to mux the nonces, which makes things much
  more complicated.  And we can't simply declare that all `Const_RefRoot`s
  containing the same value are the same object, because we don't have a
  generic equality test that covers all crucible types.)  This commit adds
  a simple workaround: include an explicit `len` field, which is updated
  in sync with `ptr` and `end`, and avoids the need for pointer
  arithmetic.

* Implement `str::as_bytes` via `crucible_identity_transmute` (last applied: May 16, 2023)

  This is necessary to avoid a gnarly use of `transmute`.

* Don't deallocate in `box_free` and `drop` (last applied: May 17, 2023)

  Crucible doesn't support a `deallocate` operation.

* Reimplement `from_{le,be}_bytes` (last applied: May 18, 2023)

  The actual implementations of these functions involve gnarly uses of
  `transmute`.

* Reimplement `to_{le,be}_bytes` (last applied: May 18, 2023)

  Same reasoning as above.