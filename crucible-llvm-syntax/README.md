# crucible-llvm-syntax

This package provides concrete syntax for Crucible-LLVM types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types, primitive atoms, and
statements:

**Types**:

- `(Ptr n)` for a positive numeral `n` represents the type of LLVM pointers that are `n` bits wide. For example `(Ptr 8)` is the type of bytes.

**Primitive atoms**:

- `none : Alignment`: no alignment
- `i8 : LLVMType`
- `i16 : LLVMType`
- `i32 : LLVMType`
- `i64 : LLVMType`
- `ptr : LLVMType`

**Statements**:

If the numeral representing `w` the pointer width and `n` is an arbitrary numeral,

- `ptr : Nat -> Bitvector w -> Ptr w`: construct a pointer from a block and offset
- `ptr-block : Ptr n -> Nat`: get the block number of a pointer
- `ptr-offset : Ptr n -> Bitvector n`: get the offset of a pointer
- `ptr-ite : Bool -> Ptr n -> Ptr n -> Ptr n`: if-then-else for pointers
- `alloca : Alignment -> BV w -> Ptr w`: allocate space on the stack
- `load : Alignment -> LLVMType -> Ptr w -> T`: load a value from memory, where the type `T` is determined by the `LLVMType`
- `store : Alignment -> LLVMType -> Ptr w -> T -> Unit`: store a value to memory, where the type `T` is determined by the `LLVMType`

[syn]: ../crucible-syntax
