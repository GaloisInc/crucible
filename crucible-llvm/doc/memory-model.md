Overview
--------

The various Crucible frontends handle memory differently.  In the simplest cases (e.g., Java and Matlab), memory is "well behaved" and can be represented with just Crucible references, which allow objects to be passed as in a by-reference language like Java.  Handling memory operations for a language like C or C++ is much more involved, and not something that core Crucible supports out of the box.  Major challenges include:

- C programs can take the address of elements in the middle of a struct or allocation
- Values written at one type can be read out at another type
- A single read can span multiple logical entities (e.g., if two `uint32_t`
  values are adjacent in a struct, a single read could return two bytes from
  each as a different `uint32_t`).

The data structure to support this more flexible view of memory is implemented in crucible-llvm.  That package has multiple components including: the translation from LLVM into Crucible, the data types supporting the translation, and Crucible overrides implementing various LLVM intrinsic operations.  The data types are of primary interest here; they are defined in the MemModel module (`Lang.Crucible.LLVM.MemModel`).

LLVM Memory Model Concept
=========================

To support the complexities of a C-like memory model, we represent memory as a log of writes.  Writes are added to the write log (with some simplifications when possible).  Reads traverse the write log backwards until the read is fully-covered.  Symbolic reads can be very expensive in this model.

Each *allocation* in the memory model is completely isolated from all other allocations, and has a unique block identifier.  Pointers into the memory model have two components: the identifier of the block they reference and an offset into that block.  Note that both the identifier and the offset can be symbolic.  The LLVM memory model handles all of the necessary logic to make that safe: reads from symbolic pointers are reduced to a mux of reads over all possible allocations (which is correct but a recipe for a bad time).  Note that all read operations generate well-formedness side conditions.  For example, reading from the pointer `{blockId: 5, offset: 100}` generates an assertion (to be discharged by the symbolic execution engine/SMT solver) that 100 is a valid offset in block 5; these side conditions are discharged statically where possible, but may become proof obligations.

The memory model is actually *used* at translation and simulation time.  LLVM (and machine code) is translated into Crucible IR such that all memory references manipulate the global memory model.  Operationally, a memory write looks something like:

```
memModel <- readGlobal MEM
memModel' <- writeMemory val addr memModel
writeGlobal MEM memModel'
```

where `MEM` is a Crucible global variable initialized with a memory model instance before symbolic execution starts.  That initial memory model usually contains some initial values (e.g., read only memory is taken from the original binary and concrete, while mutable data might be there, but with symbolic values).  Reads are similar, except they do not return an updated memory model value.

Allocating memory has two phases:

1. Actual allocation of a region using a function like `doMalloc` (`Lang.Crucible.LLVM.MemModel.doMalloc`)

   This creates a fresh allocation with no contents.  Reading from a raw allocation with no writes to it yields an error.

2. Putting data into the allocation

   Data stored into an allocation can be read back later.  The story about what is in an allocation is actually slightly complicated these days.  There are two kinds of memory:

   2a. The original memory model, where offset calculations are all resolved in Haskell code, are triggered by storing values into an allocation using `doStore` (`Lang.Crucible.LLVM.MemModel.doStore`).  This approach is nice in that mostly concrete memory operations can be resolved in Haskell and generate very simple SMT problems.  However, it behaves very badly with symbolic reads and can easily consume all memory generating symbolic terms.

   2b. The more recent symbolic memory model pushes all offset calculations for an allocation down to the SMT theory of arrays.  This behavior is triggered by initializing an allocation with an SMT array via `doArrayStore` (`Lang.Crucible.LLVM.MemModel.doArrayStore`).

There is also some special handling in the memory model for `memset` and `memcpy` to enable them to handle allocations of symbolic length.  There is a ton of complexity in the memory model not covered in this overview relating to, among other things:

- Ensuring alignment restrictions are obeyed
- Catching C undefined behavior (which is tricky, given that at the level of LLVM and machine code, compilers sometimes violate these things)
- Additional well-formedness checking (e.g., read only allocations)
- Detailed discussion of how values are reconstructed
- Optimizations that coalesce operations when it is safe

Note that this memory model is used for both LLVM and machine code (via macaw-symbolic).

Relevant Types
==============

The types used by the LLVM memory model are defined as Crucible intrinsic types for the LLVM extension.  This means that they can be split and merged just like any other value and can be passed around as first-class values in the simulator.

- `LLVMPointer` (in `Lang.Crucible.LLVM.MemModel.Pointer`)

  This is a pair of block ID number and an offset into the block.

- `Mem` (in `Lang.Crucible.LLVM.MemModel.Generic`)

  This is the log of all writes in the memory model.  It manages merging branches and all lookups are done through this data structure.

Note that many of the core operations are defined in `Lang.Crucible.LLVM.MemModel.Generic`; this module hierarchy is a bit of a legacy of multiple rounds of refactoring.
