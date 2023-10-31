# crucible-llvm-syntax

This package provides concrete syntax for Crucible-LLVM types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and statements:

**Types**:

- `(Ptr n)` for a positive numeral `n` represents the type of LLVM pointers that are `n` bits wide. For example `(Ptr 8)` is the type of bytes.

**Statements**:

- `null : Ptr n` is the null pointer, i.e. the pointer with both block number and offset concretely set to zero. The width of the null pointer is determined by the `?ptrWidth` implicit parameter used when constructing the `ParserHooks`

[syn]: ../crucible-syntax
