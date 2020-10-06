# Overview

The `crux-llvm` tool (and corresponding C library) are intended for
verifying C programs containing inline specifications (in the form of
function calls to create non-deterministic values and assert
properties).

# Prerequisites

Before running `crux-llvm`, you'll need to install the following
software:

* GHC and `cabal`, preferably using `ghcup`:
  <https://www.haskell.org/ghcup/>

* The Yices SMT solver: <http://yices.csl.sri.com/>

* The Z3 SMT solver: <https://github.com/Z3Prover/z3/releases>

* The Clang compiler: <http://releases.llvm.org/download.html>

We have tested `crux-llvm` most heavily with GHC 8.6.5 and GHC 8.8.4,
and `cabal` version 3.2.0.0. We recommend Yices 2.6.x, and Z3 4.8.x.
Technically, only one of Yices or Z3 is required, and CVC4 will work, as
well. However, in practice, having both tends to be convenient. Finally,
LLVM versions from 3.6 through 10 are likely to work well, and any
failures with versions in that range should be considered
[bugs](https://github.com/GaloisInc/crucible/issues).

# Building

The `crux-llvm` tool can be built by doing the following:

* Clone the enclosing `crucible` repository:

        git clone https://github.com/GaloisInc/crucible.git

* Change to the `crux-llvm` directory and run the build script:

        cd crucible/crux-llvm
        cabal v2-build

This will compile `crux-llvm` and supporting libraries such that they
can be executed with `cabal v2-run`. To install the binaries in the
standard Cabal binary path, run the following:

        cabal v2-install exe:crux-llvm --overwrite-policy=always

You can also use the `--installdir` flag to install binaries in a
different location.

# Invocation

In the `crux-llvm` directory (either in the repository or the root of
the directory extracted from a distribution tarball), to analyze
`file.c`, run

        crux-llvm file.c

You'll see output indicating the progress of analysis, how many proof
goals are generated, and how many were successfully proved. In addition,
the `results` directory will contain a subdirectory for the file you
provided. This directory will contain an `index.html` file that shows a
visualization of proof results overlaid on the C source code. If
`crux-llvm` found a counter-example to any of the attempted proofs, the
values of that counter-example will be overlaid on the source code (at
the location of calls to create non-deterministic values), and the
following two executable files will also exist in the `results`
directory:

* `debug-NNN`: an executable file that runs the program and provides it
  with the counter-example values. The number `NNN` indicates the line
  of the source on which the error occurred (and where it may make sense
  to set a breakpoint in a debugger to examine the state of the
  program).

* `print-model-NNN`: an executable file that prints out the values
  associated with the counter-example.

To define properties and assumptions about the code to analyze, you may
have to annotate the source code with inline properties. The following
simple example is included in the `crux-llvm` distribution.

~~~~ .c
#include <stdint.h>
#include <crucible.h>

int8_t f(int8_t x) {
  return x + 1;
}

int main() {
  int8_t x = crucible_int8_t("x");
  assuming(x < 100);
  check(f(x) < 100);
  return 0;
}
~~~~

This file includes the `crucible.h` header file that declares functions
and macros such as `crucible_int8_t`, `assuming`, and `check`. The call
to `crucible_int8_t` marks variable `x` as a symbolic variable whose
value can be any 8-bit signed integer. The C expression within the
assuming statement states that `x` must be less than 100. The expression
within the check statement is a proof goal: `crux-llvm` will attempt to
prove that property `f(x) < 100` holds whenever the assumption on `x` is
satisfied. The proof will fail in this case and `crux-llvm` will produce
a counterexample.

# API

The `crux-llvm` [header file](c-src/includes/crucible.h) contains
declarations of several functions that can be used to describe the
properties of a program that you would like to prove.

* The `crucible_assume` function states an assumption as a C expression.
  Any proofs after this point will assume this expression is true. The
  macro `assuming` will automatically fill in its location arguments.

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

* The `__VERIFIER_nondet_*` functions create non-deterministic values of
  the corresponding type. These symbolic values all have the name `x`.
  To supply distinct names, use the `crucible_*_t` functions, instead.

Note that support for the SV-COMP API exists primarily for backward
compatibility, since a large number of benchmarks already exist in that
form. The `crucible.h` API allows for better explanations by a) allowing
user-specified names for non-deterministic variables, and b) ensuring
that the conditions used in assertions are directly available and not
obscured by a conditional wrapper around an error function.

# Standard C and C++ Libraries

The code supplied to `crux-llvm` should be largely self-contained,
without calls to external code. However, some standard library functions
have built-in support. For C code, the following functions are understood:

* `__assert_rtn`
* `calloc`
* `free`
* `getenv` (always returns `NULL`)
* `malloc`
* `memcpy`
* `__memcpy_chk`
* `memmove`
* `memset`
* `__memset_chk`
* `posix_memalign`
* `printf` (supports a subset of standard printf formatting codes)
* `__printf_chk`
* `putchar`
* `puts`
* `realloc`
* `strlen`

In addition, the following LLVM intrinsic functions are supported:

* `llvm.assume`
* `llvm.bitreverse.*`
* `llvm.bswap.*`
* `llvm.ctlz.*`
* `llvm.ctpop.*`
* `llvm.cttz.*`
* `llvm.expect.*`
* `llvm.invariant.end.*`
* `llvm.invariant.start.*`
* `llvm.lifetime.end.*`
* `llvm.lifetime.start.*`
* `llvm.memcpy.*`
* `llvm.memmove.*`
* `llvm.memset.*`
* `llvm.objectsize.*`
* `llvm.sadd.with.overflow.*`
* `llvm.smul.with.overflow.*`
* `llvm.ssub.with.overflow.*`
* `llvm.stackrestore`
* `llvm.stacksave`
* `llvm.uadd.with.overflow.*`
* `llvm.umul.with.overflow.*`
* `llvm.usub.with.overflow.*`
* `llvm.x86.pclmulqdq`
* `llvm.x86.sse2.storeu.dq`

For C++ code, several core functions have built-in support, but
`crux-llvm` will also link with a precompiled LLVM bitcode file
containing the `libc++` library included with the `clang` compiler, so
most C++ code that doesn't use third-party libraries should work.

# Command-line Flags

The most important and only required argument to `crux-llvm` is the
source file or list of source files to analyze. In the case that
multiple files are provided, they will be compiled independently and
linked together with `llvm-link`.

In addition, the following flags can optionally be provided:

* `--help`, `-h`, `-?`: Print all options with brief descriptions.

* `--version`, `-V`: Show the version of the tool.

* `--config=FILE`: Load configuration from `FILE`. A configuration file
  can specify the same settings as command-line flags. Details of the
  format for configuration files appear in the next section.

* `--sim-verbose=NUM`, `-d NUM`: Set the verbosity level of the symbolic
  simulator to `N`.

* `--path-sat`: Enable path satisfiability checking, which can help
  programs terminate, particularly in the case where the bounds on loops
  are complex.

* `--output-directory=DIR`: Set the directory to use to store output
  files (default: `results`).

* `--profile-crucible`: Enable profiling of the symbolic execution
  process. Produces an additional HTML file in the output directory that
  provides a graphical and tabular depiction of the execution time
  profile.

* `--profile-solver`: Include profiling of SMT solver calls in the
  symbolic execution profile.

* `--timeout=N`, `-t N`: Set the timeout for the first phase of analysis
  (symbolic execution) which happens before sending the main goals to an
  SMT solver. Setting this to a low value can give you a result more
  quickly, but the result is more likely to be "Unknown" (default: 60).

* `--goal-timeout=N`: Set the timeout for each call to the SMT solver to
  `N` seconds.

* `--path-strategy=STRATEGY`: Set the strategy to use for exploring
  paths during symbolic execution. A `STRATEGY` of `always-merge` (the
  default) causes all paths being explored to be merged into a single
  symbolic state at every post-dominator node in the control flow graph.
  The `split-dfs` strategy explores each path independently in
  depth-first order. The former is typically more appropriate for full
  verification whereas the latter can be more effective for bug finding.
  Sometimes, however `split-dfs` can lead to faster full verification
  times.

* `--profiling-period=N`, `-p N`: Set how many seconds to wait between
  each dump of profiling data (default: 5). Intermediate profiling data
  can be helpful for diagnosing a run that does not terminate in a
  reasonable amount of time.

* `--iteration-bound=N`, `-i N`: Set a bound on the number of times a
  single loop can iterate. This can also make it more likely to get at
  least a partial verification result for complex programs, and can be
  more clearly connected to the execution of the program than a
  time-based bound.

* `--recursion-bound=N`, `-i N`: Set a bound on the number of times a
  single function can recur. This can also make it more likely to get at
  least a partial verification result for complex programs, and can be
  more clearly connected to the execution of the program than a
  time-based bound.

* `--no-execs`, `-x`: Do not create executables to demonstrate
  counter-examples.

* `--solver=NAME`, `-s NAME`: Use the given SMT solver to discharge
  proof obligations. Valid values for `NAME` are `cvc4`, `yices`, and
  `z3`.

* `--mcsat`: Enable the MC-SAT engine when using the Yices SMT solver.
  This disables the use of UNSAT cores, so the HTML rendering of proved
  goals won't include highlighting a set of the assumptions that were
  necessary for proving the goal.

* `--include-dirs=DIRS`, `-I DIRS`: Set directories to search for C/C++
  include files. This will be passed along to `clang`.

* `--lax-pointers`: Allow order comparisons between pointers from
  different allocation blocks.

# Environment Variables

The following environment variables are supported:

* `CLANG`: Specify the name of the `clang` compiler command used to
  translate from C/C++ to LLVM.

* `CLANG_OPTS`: Specify additional options to pass to `clang`.

* `LLVM_LINK`: Specify the name of the `llvm-link` command used to
  combine multiple LLVM bitcode files.

# Configuration Files

In addition to command-line flags and environment variables, `crux-llvm`
can be configured with a key-value input file. The file consists of a
set of `KEY: VALUE` entries, each on a separate line, where each `KEY`
generally corresponds to the textual part of the long version of a
command-line flag. For example, one can set the iteration bound to 10 as
follows:

    iteration-bound: 10

Options that take a list of arguments can be written with either a
single value (for a list of length one) or with multiple values on
successive lines, each starting with `*`. For example, the following is
a valid input file:

    llvm-link: "llvm-link-6.0"
    clang: "clang-6.0"
    make-executables: no
    files:
      * "a.c"
      * "b.c"

This specifies the name of the command to run for `clang` and
`llvm-link`, instructs `crux-llvm` not to create counter-example
demonstration executables, and provides a list of input files.

# Acknowledgements

Crux is partly based upon work supported by the Defense Advanced
Research Projects Agency (DARPA) under Contract No. N66001-18-C-4011.
Any opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily reflect
the views of the Defense Advanced Research Projects Agency (DARPA).
