# crux-mir

<img src="../doc/crux.svg" alt="Crux logo" width="25%" />

This is a static simulator for Rust programs.  It runs a set of test cases and
attempts to prove that all assertions pass on all valid inputs.

See our 2-minute [demo video][video] for an example of `crux-mir`'s basic
functionality.

[video]: https://www.youtube.com/watch?v=dCNQFHjgotU


## Prerequisites

You will need to install the following software:

* GHC and `cabal`. We recommend using `ghcup`:
  <https://www.haskell.org/ghcup/>

* The Yices SMT solver: <http://yices.csl.sri.com/>

* The Z3 SMT solver: <https://github.com/Z3Prover/z3/releases>

* The Rust toolchain currently supported by `mir-json`; see
  [the `mir-json` README][mir-json-readme].


## Setup: `mir-json`

`crux-mir` uses several submodules, so make sure they're initialized:

    $ git submodule update --init

Next, navigate to the `crucible/dependencies/mir-json` directory. Install
`mir-json`, translate its standard libraries, and define the
`CRUX_RUST_LIBRARY_PATH` environment variable according to the instructions in
[the `mir-json` README][mir-json-readme].

Currently, `crux-mir` supports [version
1](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#1) of
`mir-json`'s schema. Note that the schema versions produced by `mir-json` can
change over time as dictated by internal requirements and upstream changes. To
help smooth this over:

* We intend that once `crux-mir` introduces support for any given schema
  version, it will retain that support across at least two releases.
* An exception to this rule is when `mir-json` updates to support a new Rust
  toolchain version. In general, we cannot promise backwards compatibility
  across Rust toolchains, as the changes are often significant enough to impeded
  any ability to reasonably provide backwards-compatibility guarantees.

As a general policy, `crux-mir` strives to support the `mir-json` schema
versions corresponding to the last two `crux-mir` releases.

[mir-json-readme]: https://github.com/GaloisInc/mir-json#readme


## Setup: Build and Install

Use GHC 9.6, 9.8, or 9.10. From the `crux-mir` directory, run:

    $ cabal install exe:crux-mir --overwrite-policy=always


## Usage

### Writing test cases

`crux-mir` looks for functions with the `#[crux::test]` attribute and runs them
as tests.  You may need to add `#![feature(custom_attribute)]` to the crate
root to use the `#[crux::test]` attribute.  These can both be conditionally
compiled by checking for the `crux` configuration predicate using
`#[cfg_attr(crux, crux::test)]`.

Test cases can create and manipulate symbolic values using the functions in the
[`crucible`](https://github.com/GaloisInc/mir-json/tree/master/libs/crucible)
Rust crate.  See [`example/ffs/lib.rs`](example/ffs/lib.rs) or the files in
[`test/symb_eval/`](test/symb_eval) for examples of creating symbolic values
and asserting properties about them.

### Running on a Cargo project

Set the `CRUX_RUST_LIBRARY_PATH` environment variable to the path to the
translated libraries:

    $ export CRUX_RUST_LIBRARY_PATH=<mir-json checkout>/rlibs

In the directory of a Cargo project (such as the [find-first-set
example](example/ffs)), run the project's symbolic tests:

    $ cargo crux-test

`cargo-crux-test` (part of `mir-json`) will translate the code to MIR, then
invoke `crux-mir` to symbolically simulate the test cases.

### Running on a single file

To compile and test a single Rust program:

    $ cabal exec -- crux-mir test/conc_eval/prim/add1.rs

(Should print 2.)


## Examples

The [example/ffs/](example/ffs) directory in this repository contains a simple
library with concrete and symbolic tests.  Use `cargo crux-test` to run the
symbolic test, which proves that an optimized find-first-set function is
equivalent to a simple reference implementation.

A fork of the curve25519-dalek library with symbolic tests for the `Scalar52`
type is available [here][dalek-fork].  This is the code that appears in the
[`crux-mir` demo video][video].

[dalek-fork]: https://github.com/GaloisInc/curve25519-dalek


## Test suite

To run `crux-mir`'s test suite:

    $ cabal test

You need to have built and installed the mir-json tool such that it can be
found on your $PATH. You also need translated libraries for the Rust target
architecture you're testing on. See the "Preliminaries" section above for more
details.

### Expected Failures

Some tests are not yet expected to succeed, as crux-mir is still under
development. These tests are marked accordingly, so that the entire
test suite is still expected to pass.

Files that are not yet expected to work correctly begin with `// FAIL: ` and
a brief comment describing the reason for the expected failure.


## Limitations

`crux-mir` does not support reasoning about certain types of unsafe code.  Many
functions in the standard library rely on unsafe code; we have reimplemented
some of these in terms of safe code or custom `crux-mir` intrinsics, but many
unsupported functions still remain.  Test cases that call into unsupported code
will produce assertion failures with messages like `don't know how to call
core::intrinsics::transmute`.

Currently, `crux-mir` also has trouble supporting references and function
pointers in constant expressions and static initializers.
