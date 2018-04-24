Introduction
-------------

Crucible is a language-agnostic library for performing forward
symbolic execution of imperative programs.  It provides a collection of
data-structures and APIs for expressing programs as control-flow
graphs.  Programs expressed as CFGs in this way can be automatically
explored by the symbolic execution engine.  In addition, new data
types and operations can be added to the symbolic simulator by
implementing fresh primitives directly in Haskell.  Crucible also
provides connections to a variety of SAT and SMT solvers that can be
used to perform verification and find counterexamples to logical
conditions computed from program simulation.

Crucible has been designed as a set of Haskell packages organized so that Crucible
itself has a minimal number of external dependencies, and functionality
independent of crucible can be separated into sub-libraries.

Currently, the repo consists of the following Haskell packages:

 * **`crucible`** provides the core Crucible definitions, the
   symbolic simulator, the `SimpleBackend` formula representation, interfaces
   between `SimpleBackend` and SMT solvers, and an LLVM-to-Crucible translator.
 * **`crucible-abc`** provides functionality for generating
   ABC networks from `SimpleBackend` expressions.
 * **`crucible-blt`** provides functionality for generating
   BLT problems from `SimpleBackend` expressions.
 * **`crucible-saw`** provides functionality for generating
   SAW Core terms from Crucible Control-Flow-Graphs.
 * **`galois-matlab`** provides a few data structures for working with
   MATLAB values.

In addition, there is the following library/executable package:

 * **`crucible-server`**, a standalone process that allows constructing
   and symbolically executing Crucible programs via [Protocol Buffers][pb].
   The crucible-server directory also contains a Java API for
   connecting to and working with the `crucible-server`.

[pb]: https://developers.google.com/protocol-buffers/ "Protocol Buffers"


The development of major features and additions to `crucible` is done
in separate branches of the repository, all of which are based off
`master` and merge back into it when completed. Minor features and bug
fixes are done in the `master` branch. Naming of feature branches is
free-form.

Each library is BSD-licensed (see the `LICENSE` file in a project
directory for details).

Quick start
-------------


Crucible is mainly intended to be used as a libarary for other
downstream projects.  As such, the build system infrastructure in this
repository is relatively minimal. Downstream projects are expected to
do the primary work of tracking dependencies, and mantaining a
coherent working set of git submodules, etc.

However, for convenience, we provide here some basic support for
building crucible in place.

To fetch all the latest git versions of immediate dependencies of
libraries in this repository, use the `scripts/build-sandbox.sh` shell
script.  You will find it most convenient to setup public-key login
for GitHub before you perform this step.

Now, you may use either `stack` or `cabal new-build` to compile the
libraries, as you prefer.

```
./scripts/build-sandbox.sh
stack setup
stack build
```

```
./scripts/build-sandbox.sh
cabal update
cabal new-configure
cabal new-build all
```

The build depends on having `hpb` in your path. After fetching the
dependencies, this can be arranged by entering `dependencies/hpb/` and
running the following commands:
```
cabal sandbox init
cabal install --dependencies-only
cabal install
cp ./cabal-sandbox/bin/hpb ⟨EXE_PATH⟩
```
where `⟨EXE_PATH⟩` is a directory on your `$PATH`.
