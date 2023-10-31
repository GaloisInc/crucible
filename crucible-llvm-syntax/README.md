# crucible-llvm-syntax

This package provides concrete syntax for Crucible-LLVM types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and statements:

**Types**:

- `(Ptr n)` for a positive numeral `n` represents the type of LLVM pointers that are `n` bits wide. For example `(Ptr 8)` is the type of bytes.

**Statements**:

- `ptr : Nat -> Bitvector w -> Ptr w`: construct a pointer from a block and offset
- `ptr-block : Ptr w -> Nat`: get the block number of a pointer
- `ptr-offset : Ptr w -> Bitvector w`: get the offset of a pointer
- `ptr-ite : Bool -> Ptr w -> Ptr w -> Ptr w`: if-then-else for pointers

[syn]: ../crucible-syntax
