# crucible-mir-syntax

This package provides concrete syntax for Crucible-MIR types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types, primitive atoms, and
statements:

**Types**:

- `MirReference` represents the type of MIR references and pointers. Note that
  `MirReference` does _not_ record the type of the underlying memory, as that
  information is determined when performing reference-related operations (e.g.,
  `ref-read` or `ref-write`).

**Statements**:

- `ref-new : Type -> MirReference`: construct a new reference that points to
   a temporary value of given `Type`. By convention, this reference should be
   dropped (using `ref-drop`) when the temporary value goes out of scope.
- `ref-read : Type -> MirReference -> T`: read a value from a reference, where
   where the return type `T` is determined by the `Type` argument.
- `ref-write : Type -> MirReference -> T -> ()`: write a value to a reference,
   where the return type `T` is determined by the `Type` argument.
- `ref-drop : MirReference -> ()`: drop a reference when the underlying value
  goes out of scope.

`Type` signifies a Crucible type, rather than an MIR type. This means there
are no Rust- or MIR-like `Type`s such as `&i8` or `usize`, but rather the base
Crucible types as defined by `crucible-syntax`, and `MirReference`.

[syn]: ../crucible-syntax
