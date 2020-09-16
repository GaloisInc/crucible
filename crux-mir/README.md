# crux-mir

This is a static simulator for Rust programs.  It runs a set of test cases and
attempts to prove that all assertions pass on all valid inputs.

See our 2-minute [demo video][video] for an example of `crux-mir`'s basic
functionality.

[video]: https://www.youtube.com/watch?v=dCNQFHjgotU


## Preliminaries

You must have the most recent version of the `mir-json` executable in your
path.  See [the `mir-json` README][mir-json-readme] for installation
instructions.

`crux-mir` uses several submodules, so make sure they're initialized:

    $ git submodule update --init

[mir-json-readme]: https://github.com/GaloisInc/mir-json#readme


## Installation

Use ghc-8.4.4 or ghc-8.6.5.

    $ cabal v2-build

Then translate the Rust libraries in `lib/`:

    $ ./translate_libs.sh


## Usage

### Writing test cases

`crux-mir` looks for functions with the `#[crux_test]` attribute and runs them
as tests.  You may need to add `#![feature(custom_attribute)]` to the crate
root to use the `#[crux_test]` attribute.  These can both be conditionally
compiled by checking for `#[cfg(crux)]`.

Test cases can create and manipulate symbolic values using the functions in the
[`crucible`](lib/crucible) Rust crate.  See
[`example/ffs/lib.rs`](example/ffs/lib.rs) or the files in
[`test/symb_eval/`](test/symb_eval) for examples of creating symbolic values
and asserting properties about them.

### Running on a Cargo project

First, install the `crux-mir` binary to your `~/.cabal/bin` directory:

    $ cabal v2-install crux-mir

Set the `CRUX_RUST_LIBRARY_PATH` environment variable to the path to the
translated libraries:

    $ export CRUX_RUST_LIBRARY_PATH=.../crux-mir/rlibs

In the directory of a Cargo project (such as the [find-first-set
example](example/ffs)), run the project's symbolic tests:

    $ cargo crux-test

`cargo-crux-test` (part of `mir-json`) will translate the code to MIR, then
invoke `crux-mir` to symbolically simulate the test cases.

### Running on a single file

To compile and test a single Rust program:

    $ cabal v2-exec -- crux-mir test/conc_eval/prim/add1.rs

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

To run the tests:

    $ cabal v2-test

### Expected Failures

Some tests are not yet expected to succeed, as crux-mir is still under
development. These tests are marked accordingly, so that the entire
test suite is still expected to pass.

Files that are not yet expected to work correctly begin with `// FAIL: ` and
a brief comment describing the reason for the expected failure.


## Limitations

`crux-mir` does not support reasoning about unsafe code.  Many functions in
the standard library rely on unsafe code; we have reimplemented some of these
in terms of safe code or custom `crux-mir` intrinsics, but many unsupported
functions still remain.  Test cases that call into unsafe code will produce
assertion failures with messages like `don't know how to call
core::intrinsics::transmute` or `expected reference type in dereference
TyRawPtr`.

Currently, `crux-mir` also has trouble supporting references and function
pointers in constant expressions and static initializers.
