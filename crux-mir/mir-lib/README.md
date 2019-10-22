This rust cargo contains a single file `src/lib.rs` that is used to
define the standard library for mir-verifier.

This file is derived from the modules in
https://github.com/rust-lang/rust/tree/master/src/libcore, in
accordance with the MIT LICENCE.

==================================================================

How to add new pieces of libcore to mir-lib:

 - Add the new file to the crate through normal `mod` items.  If the
   new file needs features not already enabled, add the extra
   `#![feature]` attributes to `lib.rs`.

 - Leave any stability attributes intact.  Unfortunately, stability
   attributes are mandatory everywhere when `#![feature(staged_api)]`
   is enabled, and are forbidden everywhere when it's disabled.  (It
   seems easier to leave it enabled, since most code is copied from
   libcore and thus already has stability attributes.)

 - `#[lang]` attrs should be commented or `#[cfg_attr]`'d out, instead
   of being deleted entirely.  This part isn't essential, but will
   make it easier to re-enable all the lang items in the future.

Note from Stuart: If we ever get mir-lib to a state where it's fully
self-contained (no imports from `core`, only from other mir-lib
modules) and has implementations of all the essential lang items, then
we can switch from `#[no_std]` to `#[no_core]`.  We'd also need to
re-enable all the `#[lang]` items as part of that change, which is why
it would be nice to leave them in place.  Making the switch would
allow mir-lib to implement some additional pieces, such as the
overlapping slice impls noted previously.

(The alternative to finishing mir-lib would be to make the verifier
replace functions that have translation errors with `assert!(false)`,
so we could translate libcore directly.  I'm not sure which way would
be easier.)



