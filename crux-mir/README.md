# crux-mir

This is a static simulator for Rust programs.  It runs a set of test cases and
attempts to prove that all assertions pass on all valid inputs.

See our 2-minute [demo video][video] for an example of `crux-mir`'s basic
functionality.

[video]: https://www.youtube.com/watch?v=dCNQFHjgotU


## Preliminaries

`crux-mir` uses several submodules, so make sure they're initialized:

    $ git submodule update --init

Next, navigate to the `crucible/dependencies/mir-json` directory and install
`mir-json` according to the instructions in [the `mir-json`
README][mir-json-readme].

[mir-json-readme]: https://github.com/GaloisInc/mir-json#readme


## Installation

Use GHC 9.2, 9.4, or 9.6. From the `crux-mir` directory, run:

    $ cabal v2-install exe:crux-mir --overwrite-policy=always

Then translate the Rust libraries in `lib/`:

    $ ./translate_libs.sh

If you want to cross-compile for a different target, you can optionally set the
environment variable `TARGET` to a [target
triple](https://doc.rust-lang.org/nightly/rustc/platform-support.html) when
running `./translate_libs.sh`. This is experimental and we have only tested
`wasm32-unknown-unknown` to work; you might get build errors for other targets.

    $ TARGET=wasm32-unknown-unknown ./translate_libs.sh

When upgrading from a previous version, first install the new `mir-json`
version, then rerun the `cabal v2-install` and `./translate_libs.sh` commands.


## Usage

### Writing test cases

`crux-mir` looks for functions with the `#[crux::test]` attribute and runs them
as tests.  You may need to add `#![feature(custom_attribute)]` to the crate
root to use the `#[crux::test]` attribute.  These can both be conditionally
compiled by checking for the `crux` configuration predicate using
`#[cfg_attr(crux, crux::test)]`.

Test cases can create and manipulate symbolic values using the functions in the
[`crucible`](lib/crucible) Rust crate.  See
[`example/ffs/lib.rs`](example/ffs/lib.rs) or the files in
[`test/symb_eval/`](test/symb_eval) for examples of creating symbolic values
and asserting properties about them.

### Running on a Cargo project

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

To run `crux-mir`'s test suite:

    $ cabal v2-test

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
