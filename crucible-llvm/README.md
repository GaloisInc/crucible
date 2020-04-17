This package implements an LLVM frontend for Crucible.  The frontend provides two major things:
1. A translation of LLVM IR into the Crucible IR
2. Data types supporting that translation

Most clients of the library that just want to analyze LLVM IR (which usually means C and C++) will only need the `Lang.Crucible.LLVM` and `Lang.Crucible.LLVM.Translation` modules.  The core data structure implementing the LLVM memory model (see `Lang.Crucible.LLVM.MemModel`) may be of interest to other clients.  The memory model is documented in more detail in [the docs](doc/memory-model.md).
