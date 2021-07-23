This repository provides primitives for supporting symbolic I/O in Crucible.

These primitives are intended to be language-agnostic.  They reflect the services provided by a typical operating system, currently with a focus on file input and output.  The supported I/O operations are symbolic in that the provided file abstraction can have both concrete and symbolic contents.

As motivation, these primitives can be used to verify programs that e.g., have configuration files or read data from the filesystem.  As the files can have symbolic contents, this could enable verifying families of configurations (i.e., configuration files with symbolic fields).

# Implementation

The primitives in this library make the observation that a file is essentially an extra (disjoint) memory allocation, which can be modeled in a similar way as a low-level byte-oriented memory model.  This library implements a custom memory model to support files; it is inspired by the LLVM memory model in crucible-llvm, but is separate because:

- It can be simplified without needing to support LLVM-specific details or structures (e.g., it is only byte oriented and does not need any of the LLVM type information)
- A separate backing store enables this library to be independent of crucible-llvm, and thus reusable in more contexts

Each file is represented as a log of writes that coalesces adjacent entries where possible, as well as a (symbolic) pointer to the "current" location in the file.  The backing store is an SMT array.  This structure supports mixed symbolic and concrete reads and writes.  A filesystem is a collection of files associated with (absolute) file paths.

The primitives are implemented as language extension independent overrides.

# Using Symbolic I/O

The provided primitives support:
- Opening files (based on a path name)
- Reading from files that have been opened
- Writing to files that have been opened
- Closing files

To be used in a language-specific instantiation of Crucible, these primitives must be wrapped in overrides for the target language.  See crucible-llvm for an example of wrapping these low-level primitives for use in a language-specific instantiation of Crucible.

# Limitations

The library does not currently support any of the following, but would like to:

- File permissions
- Seek/Tell operations (e.g., arbitrary modifications to the file pointer)
- Relative paths
- File truncation
- Text files with symbolic fields (e.g., port numbers) are difficult to represent
