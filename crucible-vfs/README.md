Prototype implementation of a virtual filesystem based on the LLVM memory model.

The VFS has a unique copy of the underlying memory representation for LLVM, using
it as a persistence layer and building a filesystem abstraction on top of it.

The filesystem is initialized by associating file names with globally-allocated
memory blocks. When a file is "opened", the file contents are copied from this block
to a fresh heap-allocated block, returning a file handle.

A file handle is a mutable reference to a pointer. Initially it points to the start
of a file, but each file operation increments the pointer based on the number of bytes
read or written. Reads and writes (as well as the initial file contents) are represented
as a vector of bytes.

Closing a file handle copies the contents of the heap-allocated block back to the global
block (i.e. flushing the write buffer). The heap-allocated block is freed and the
associated file handle is invalidated by setting its underlying pointer to null.
