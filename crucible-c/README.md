The `crucible-c` tool (and corresponding C library) are intended for
verifying C programs containing inline specifications (in the form of
function calls to create non-deterministic values and assert
properties). The API defined by SV-COMP is supported, as it an
alternative, slightly more flexible API.

# Prerequisites

Before running `crucible-c`, you'll need to install the following
software:

* Yices, available from <http://yices.csl.sri.com/>

* Z3, available from <https://github.com/Z3Prover/z3/releases>

* LLVM+Clang, available from <http://releases.llvm.org/download.html>

We have tested it with Yices 2.6.0, Z3 4.7.1, and LLVM 6.0.1.

# Building

The `crucible-c` tool can be built by doing the following:

* Clone the `crucible` repository into a directory `$DIR`.

* Change to the `$DIR` directory and run

  `./scripts/build-sandbox.sh`.

* Change to the `$DIR/crucible-c` directory and run

  `cabal new-build crucible-c`

# Invocation

In the `crucible-c` directory, to analyze `file.c`, run

    cabal new-run crucible-c file.c

You'll see output indicating the progress of analysis, how many proof
goals are generated, and how many were successfully proved. In
addition, the `results` directory will contain a subdirectory for the
file you provided. This directory will contain an `index.html` file
that shows a visualization of proof results overlaid on the C source
code. If `crucible-c` found a counter-example to any of the attempted
proofs, the values of that counter-example will be overlaid on the
source code (at the location of calls to create non-deterministic
values), and the following two files will also exist in the `results`
directory:

* `debug-NNN`: an executable file that runs the program and provides it
with the counter-example values. The number `NNN` indicates the line
of the source on which the error occurred (and where it may make
sense to set a breakpoint in a debugger to examine the state of the
program).

* `print-model-NNN`: an executable file that prints out the values
associated with the counter-example.

# API

The `crucible-c` [header file](c-src/includes/crucible.h) contains
declarations of several functions that can be used to describe the
properties of a program that you would like to prove.

* The `crucible_assume` function states an assumption as a C
expression. Any proofs after this point will assume this expression
is true. The macro `assuming` will automatically fill in its location
arguments.

* The `crucible_assert` function states an property to check as a C
expression. Every call to this function will create an additional
proof goal. The `check` macro will automatically fill in its location
arguments.

* The `crucible_*_t` functions create fresh (non-deterministic) values
of the corresponding type. The verification process ensures that
whatever results are returned by these functions, out of all possible
values for the corresponding type, all `crucible_assert` calls will
succeed.

For programs that have been written for the SV-COMP competition, the
following alternative API is available.

* The `__VERIFIER_assume` function is equivalent to `crucible_assume`,
but does not take location information as an argument.

* The `__VERIFIER_error` function indicates that correct control flow
should never reach the point of the call. It is equivalent to
`check(0)`.

* The `__VERIFIER_nondet_uint` and `__VERIFIER_nondet_char` functions
create non-deterministic `unsigned int` and `char` values
respectively.
