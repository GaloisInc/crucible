# crucible-debug

`crucible-debug` is a library for interactive debugging of Crucible programs.
It is structured as an [`ExecutionFeature`][exec-feat], meaning that it can be used in situ inside of any program that uses Crucible.

[exec-feat]: https://hackage.haskell.org/package/crucible-0.7.1/docs/Lang-Crucible-Simulator.html#t:ExecutionFeature

Users interact with the debugger via a simple command language.
This language features a number of familiar commands such as setting and removing breakpoints (`break`/`delete`), printing stack traces (`backtrace`), stepping through symbolic execution (`step`), and loading debugger commands from files (`source`).
It additionally provides more Crucible-specific commands such as inspecting program CFGs (`cfg`) and printing the current path condition (`path-condition`).
All available commands can be listed using the interactive documentation system (`help`).

In addition to the library, this package provides an executable.
The executable begins the debugger inside of a "minimal" Crucible program that immediately returns the unit value `()`.
This is not very interesting on its own, but the `load` command can load Crucible S-expression programs, and the `call` command can call functions from loaded programs.

The command language can be extended by downstream packages.
Such extensions can be used to add commands that are specific to a particular Crucible syntax extension (i.e., source language).
For example, the `crucible-llvm-debug` package provides the `memory` command to print the current LLVM memory.

This tool shares some functionality with the [surveyor] project. The principal architectural distinction is that `crucible-debug` is designed to be embedded into larger tools like Crux and SAW, while `surveyor` is a standalone application.

[surveyor]: https://github.com/GaloisInc/surveyor

The test suite is described in its Haddocks.

## Acknowledgements

This material is based upon work supported by the Defense Advanced Research Projects Agency under Contract No. W31P4Q-22-C-0017 and W31P4Q-23-C-0020

Any opinions, findings and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the Defense Advanced Research Projects Agency or the U.S. Government.

Distribution Statement A. Approved for public release: distribution is unlimited.

## Copyright

Copyright (c) Galois, Inc. 2025.
