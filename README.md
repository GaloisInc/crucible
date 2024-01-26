Introduction
-------------

Crucible is a language-agnostic library for performing forward
symbolic execution of imperative programs.  It provides a collection
of data-structures and APIs for expressing programs as control-flow
graphs.  Programs expressed as CFGs in this way can be automatically
explored by the symbolic execution engine.  In addition, new data
types and operations can be added to the symbolic simulator by
implementing fresh primitives directly in Haskell.  Crucible relies on
an underlying library called [What4](https://github.com/GaloisInc/what4)
that provides formula representations, and connections to a variety of
SAT and SMT solvers that can be used to perform verification and find
counterexamples to logical conditions computed from program simulation.

Crucible has been designed as a set of Haskell packages organized so
that Crucible itself has a minimal number of external dependencies,
and functionality independent of crucible can be separated into sub-libraries.

Currently, the repository consists of the following Haskell packages:
 * **`crucible`** provides the core Crucible definitions, including the
   symbolic simulator and control-flow-graph program representations.
 * **`crucible-llvm`** provides translation and runtime support for
   executing LLVM assembly programs in the Crucible symbolic simulator.
 * **`crucible-jvm`** provides translation and runtime support for
   executing JVM bytecode programs in the Crucible symbolic simulator.
 * **`crucible-saw`** provides functionality for generating
   SAW Core terms from Crucible Control-Flow-Graphs.
 * **`crux`** provides common support libraries for running the
   crucible simulator in a basic "all-at-once" use mode for simulation
   and verification.  This includes most of the setup steps required
   to actually set the simulator off and running, as well as
   functionality for collecting and discharging safety conditions and
   generated assertions via solvers.  Both the `crux-llvm` and `crucible-jvm`
   executables are thin wrappers around the functionality provided
   by `crux`.

In addition, there are the following library/executable packages:

 * **`crux-llvm`**, a standalone frontend for executing C and C++ programs
   in the crucible symbolic simulator.  The front-end invokes `clang`
   to produce LLVM bitcode, and runs the resulting programs using
   the `crucible-llvm` language frontend.

 * **`crux-llvm-svcomp`**, an alternative entrypoint to `crux-llvm`
   that uses the protocol established for the [SV-COMP][sv-comp] competition.
   See [here](crux-llvm/README.md) for more details.

[sv-comp]: https://sv-comp.sosy-lab.org

 * **`crucible-jvm`**, also contains an executable for directly
   running compiled JVM bytecode programs, in a similar vein
   to the `crux-llvm` package.

 * **`crux-mir`**, a tool for executing Rust programs in the crucible symbolic
   simulator.  This is the backend for the `cargo crux-test` command provided
   by `mir-json`.  See the [`crux-mir` README](crux-mir/README.md) for details.

 * **`uc-crux-llvm`**, another standalone frontend for executing C and C++
   programs in the Crucible symbolic simulator, using "under-constrained"
   symbolic execution. Essentially, this technique can start at any function in
   a given program with no user intervention and try to find bugs, but may raise
   false positives and is less useful for full verification than `crux-llvm`.
   See [the README](./uc-crux-llvm/README.md) for details.

Finally, the following packages are intended primarily for use by Crucible
developers:

 * **`crucible-cli`** provides a CLI for interacting with the Crucible
   simulator, via programs written in `crucible-syntax`.

 * **`crucible-llvm-cli`** provides a CLI for interacting with the Crucible
   simulator, via programs written in `crucible-syntax` with the extensions
   provided by `crucible-llvm{,-syntax}`.

 * **`crucible-syntax`** provides a native S-Expression based concrete
   syntax for crucible programs.  It is useful for being able to
   directly interact with the core Crucible simulator without bringing
   in issues related to the translation of other front-ends (e.g. the
   LLVM translation).  It is primarily intended for the purpose of
   writing test cases.

The development of major features and additions to `crucible` is done
in separate branches of the repository, all of which are based off
`master` and merge back into it when completed. Minor features and bug
fixes are done in the `master` branch. Naming of feature branches is
free-form.

Each library is BSD-licensed (see the `LICENSE` file in a project
directory for details).

Quick start
-------------
Clone this repository and checkout the immediate submodules to supply the needed
dependencies (`git submodule update --init`).

Crucible can be built with the `cabal` tool:

```
cabal update
cabal new-configure
cabal new-build all
```

Alternately, you can target a more specific sub-package instead of `all`.

Testing and Coverage
--------------------

Testing with coverage tracking is done via `cabal test --enable-coverage ...`  or
`cabal configure --enable-coverage`, although additional workarounds will be
needed as noted in https://github.com/galoisinc/crucible/issues/884 and
https://github.com/haskell/cabal/issues/6440.

Notes on Freeze Files
---------------------

We use the `cabal.GHC-*.config` files to constrain dependency versions in CI.
We recommand using the following command for best results before building
locally:

```
ln -s cabal.GHC-<VER>.config cabal.project.freeze
```

These configuration files were generated using
`cabal freeze --enable-tests --enable-benchmarks`. Note that at present, these
configuration files assume a Unix-like operating system, as we do not currently
test Windows on CI. If you would like to use these configuration files on
Windows, you will need to make some manual changes to remove certain packages
and flags:

```
regex-posix
tasty +unix
unix
unix-compat
```

Acknowledgements
----------------

Crucible is partly based upon work supported by the Defense Advanced
Research Projects Agency (DARPA) under Contract No. N66001-18-C-4011.
Any opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily reflect
the views of the Defense Advanced Research Projects Agency (DARPA).
