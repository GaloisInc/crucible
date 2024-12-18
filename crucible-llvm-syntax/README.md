# crucible-llvm-syntax

This package provides concrete syntax for Crucible-LLVM types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types, primitive atoms, and
statements:

**Types**:

- `(Ptr n)` for a positive numeral `n` represents the type of LLVM pointers that are `n` bits wide; for example `(Ptr 8)` is the type of bytes

**Primitive atoms**:

- `none : Alignment`: no alignment
- `i8 : LLVMType`: [LLVM docs][int-type], corresponds to Crucible-LLVM's `IntType 8 :: MemType`
- `i16 : LLVMType`: [LLVM docs][int-type], corresponds to Crucible-LLVM's `IntType 16 :: MemType`
- `i32 : LLVMType`: [LLVM docs][int-type], corresponds to Crucible-LLVM's `IntType 32 :: MemType`
- `i64 : LLVMType`: [LLVM docs][int-type], corresponds to Crucible-LLVM's `IntType 64 :: MemType`
- `ptr : LLVMType`: [LLVM docs][ptr-type], corresponds to Crucible-LLVM's `PtrOpaqueType :: MemType`

[int-type]: https://llvm.org/docs/LangRef.html#integer-type
[ptr-type]: https://llvm.org/docs/LangRef.html#pointer-type

**Statements**:

If the numeral `w` is the width of a pointer and `n` is an arbitrary numeral,

- `ptr : Nat -> Bitvector n -> Ptr n`: construct a pointer from a block and offset
- `ptr-add-offset : Ptr w -> Bitvector w -> Ptr w`: add an offset to a pointer
- `ptr-block : Ptr n -> Nat`: get the block number of a pointer
- `ptr-offset : Ptr n -> Bitvector n`: get the offset of a pointer
- `ptr-ite : Bool -> Ptr n -> Ptr n -> Ptr n`: if-then-else for pointers
- `ptr-sub : Ptr w -> Ptr w -> Ptr w`: subtract two pointers
- `alloca : Alignment -> Bitvector w -> Ptr w`: allocate space on the stack
- `load : Alignment -> LLVMType -> Ptr w -> T`: load a value from memory, where the type `T` is determined by the `LLVMType`
- `load-handle : Type -> [Type] -> Ptr w -> T`: load a function handle from memory, where the type `T` is determined by the given return and argument types
- `store : Alignment -> LLVMType -> Ptr w -> T -> Unit`: store a value to memory, where the type `T` is determined by the `LLVMType`
- `resolve-global : String -> Ptr w`: get the address of a global variable

`Type` signifies a Crucible type, rather than an LLVM type. This means there
are no C- or LLVM-like `Type`s such as `i8*` or `size_t`, but rather the base
Crucible types as defined by `crucible-syntax`, and `(Ptr n)`.

## Further extensions

The LLVM parser hooks can be further customized by passing yet another `ParserHooks`
to them. The `TypeAlias` module implements one such example, for translating
types like `Long` into `(Bitvector n)` and `Pointer` into `(Ptr n)` for
appropriate `n`.

[syn]: ../crucible-syntax
