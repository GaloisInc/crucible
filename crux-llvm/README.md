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

* The Clang compiler and LLVM toolchain: <http://releases.llvm.org/download.html>

  If you are on macOS, one way to install LLVM is with [`brew`](https://brew.sh/).
  To install LLVM with `brew`, run the following commands:
   * `xcode-select --install`
   * `brew install llvm`
   * `echo 'export PATH="/usr/local/opt/llvm/bin:$PATH"' >> ~/.bash_profile`
   * run `crux-llvm` in a new console to reload `.bash_profile`

We have tested `crux-llvm` most heavily with GHC 8.6.5, GHC 8.8.4, GHC
8.10.4, and `cabal` version 3.2.0.0. We recommend Yices 2.6.x, and Z3
4.8.x. Technically, only one of Yices or Z3 is required, and CVC4 is
also supported. However, in practice, having both tends to be
convenient. Finally, LLVM versions from 3.6 through 11 are likely to
work well, and any failures with versions in that range should be
[reported as bugs](https://github.com/GaloisInc/crucible/issues).

# Building

The `crux-llvm` tool can be built by doing the following:

* Clone (incl. the submodules) the `crucible` repository:

        git clone --recursive https://github.com/GaloisInc/crucible.git

* Build the `crux-llvm` package:

        cabal build crux-llvm

This will compile `crux-llvm` and supporting libraries such that they
can be executed with `cabal run`. To install the binaries in the
standard Cabal binary path (usually `$HOME/.cabal/bin`), run the
following:

        cabal install exe:crux-llvm --overwrite-policy=always

You can also use the `--installdir` flag to install binaries in a
different location.

# Invocation

In the `crux-llvm` directory (either in the repository or the root of
the directory extracted from a distribution tarball), to analyze
`file.c`, run

        cabal run exe:crux-llvm file.c

If you've installed `crux-llvm` somewhere on your `PATH`, you can
instead run

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

To define properties and assumptions about the code to analyze, you can
annotate the source code with inline properties. When `crux-llvm`
compiles your code, it defines the CPP macro `CRUCIBLE` to help specify
Crucible-specific functionality such as inline properties. The following
simple example includes on version of `main` when running with
`crux-llvm` and different one when compiled normally.

~~~~ .c
#include <stdint.h>
#ifdef CRUCIBLE
#include <crucible.h>
#endif

int8_t f(int8_t x) {
  return x + 1;
}

#ifdef CRUCIBLE
int main() {
  int8_t x = crucible_int8_t("x");
  assuming(x < 100);
  check(f(x) < 100);
  return 0;
}
#else
int main(int argc, char **argv) {
  return f(argc);
}
#endif
~~~~

When running under `crux-llvm`, this file includes the `crucible.h`
header file that declares functions and macros such as
`crucible_int8_t`, `assuming`, and `check`. The call to
`crucible_int8_t` marks variable `x` as a symbolic variable whose value
can be any 8-bit signed integer. The C expression within the assuming
statement states that `x` must be less than 100. The expression within
the check statement is a proof goal: `crux-llvm` will attempt to prove
that property `f(x) < 100` holds whenever the assumption on `x` is
satisfied. The proof will fail in this case and `crux-llvm` will produce
a counterexample describing the case where `x` is 99.

# API

The [`crucible.h` header file](c-src/includes/crucible.h) contains
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

For programs that have been written for the [SV-COMP
competition](https://sv-comp.sosy-lab.org/), the `__VERIFIER_nondet_*`
functions create non-deterministic values of the corresponding type.
These symbolic values all have the name `x`. To supply distinct names,
use the `crucible_*_t` functions, instead.

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
* `open`
* `read`
* `write`
* `close`

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
most C++ code that doesn't use third-party libraries (or that includes
those libraries linked into a single bitcode file) should work.

# Command-line Flags

The most important and only required argument to `crux-llvm` is the
source file or list of source files to analyze. In the case that
multiple files are provided, they will be compiled independently and
linked together with `llvm-link`.

In addition, the following flags can optionally be provided:

* `--help`, `-h`, `-?`: Print all options with brief descriptions.

* `--include-dirs=DIRS`, `-I DIRS`: Set directories to search for C/C++
  include files. This will be passed along to `clang`.

* `-O NUM`: Set the optimization level for `clang`.

* `--version`, `-V`: Show the version of the tool.

* `--sim-verbose=NUM`, `-d NUM`: Set the verbosity level of the symbolic
  simulator to `N`.

* `--floating-point=FPREP`, `-f FPREP`: Select the floating point
  representation to use. The value of `FPREP` can be one of `real`,
  `ieee`, `uninterpreted`, or `default`. Default representation is
  solver specific: `real` for CVC4 and Yices, and `ieee` for Z3.

* `--iteration-bound=N`, `-i N`: Set a bound on the number of times a
  single loop can iterate. This can also make it more likely to get at
  least a partial verification result for complex programs, and can be
  more clearly connected to the execution of the program than a
  time-based bound.

* `--profiling-period=N`, `-p N`: Set how many seconds to wait between
  each dump of profiling data (default: 5). Intermediate profiling data
  can be helpful for diagnosing a run that does not terminate in a
  reasonable amount of time.

* `--quiet`, `-q`: Quiet mode; produce minimal output.

* `--recursion-bound=N`, `-i N`: Set a bound on the number of times a
  single function can recur. This can also make it more likely to get at
  least a partial verification result for complex programs, and can be
  more clearly connected to the execution of the program than a
  time-based bound.

* `--solver=NAME`, `-s NAME`: Use the given SMT solver to discharge
  proof obligations. Valid values for `NAME` are `cvc4`, `yices`, and
  `z3`.

* `--timeout=N`, `-t N`: Set the timeout for the first phase of analysis
  (symbolic execution) which happens before sending the main goals to an
  SMT solver. Setting this to a low value can give you a result more
  quickly, but the result is more likely to be "Unknown" (default: 60).

* `--no-execs`, `-x`: Do not create executables to demonstrate
  counter-examples.

* `--branch-coverage`: Record branch coverage information.

* `--config=FILE`: Load configuration from `FILE`. A configuration file
  can specify the same settings as command-line flags. Details of the
  format for configuration files appear in the next section.

* `--entry-point=SYMBOL`: Start symbolic execution at `SYMBOL`.

* `--fail-fast`: Stop attempting to prove goals as soon as one of them
  is disproved.

* `--force-offline-goal-solving`: Force goals to be solved using an
  offline solver, even if the selected solver could have been used in
  online mode.

* `--goal-timeout=N`: Set the timeout for each call to the SMT solver to
  `N` seconds.

* `--hash-consing`: Enable hash-consing in the symbolic expression
  backend.

* `--lax-arithmetic`: Allow arithmetic overflow.

* `--lax-pointers`: Allow order comparisons between pointers from
  different allocation blocks.

* `--lazy-compile`: Avoid compiling bitcode from source if intermediate
  files already exist.

* `--mcsat`: Enable the MC-SAT engine when using the Yices SMT solver.
  This disables the use of UNSAT cores, so the HTML rendering of proved
  goals won't include highlighting a set of the assumptions that were
  necessary for proving the goal.

* `--no-unsat-cores`: Disable computing unsat cores for successful
  proofs.

* `--online-solver-output=FILE`: Store a log of interaction with the
  online goal solver in `FILE`.

* `--opt-loop-merge`: Insert merge blocks in loops with early exits.

* `--output-directory=DIR`: Set the directory to use to store output
  files (default: `results`).

* `--path-sat`: Enable path satisfiability checking, which can help
  programs terminate, particularly in the case where the bounds on loops
  are complex.

* `--path-sat-solver=SOLVER`: Select the solver to use for path
  satisfiability checking, in order to use a different solver than for
  discharging goals.

* `--path-sat-solver-output`: Store a log of interaction with the path
  satisfiability solver in `FILE`.

* `--path-strategy=STRATEGY`: Set the strategy to use for exploring
  paths during symbolic execution. A `STRATEGY` of `always-merge` (the
  default) causes all paths being explored to be merged into a single
  symbolic state at every post-dominator node in the control flow graph.
  The `split-dfs` strategy explores each path independently in
  depth-first order. The former is typically more appropriate for full
  verification whereas the latter can be more effective for bug finding.
  Sometimes, however `split-dfs` can lead to faster full verification
  times.

* `--profile-crucible`: Enable profiling of the symbolic execution
  process. Produces an additional HTML file in the output directory that
  provides a graphical and tabular depiction of the execution time
  profile.

* `--profile-solver`: Include profiling of SMT solver calls in the
  symbolic execution profile.

* `--skip-incomplete-reports`: Skip reporting on proof obligations that
  arise from timeouts and resource exhaustion.

* `--skip-print-failures`: Skip printing messages related to failed
  verification goals.

* `--skip-report`: Skip producing the HTML report following
  verification.

* `--skip-success-reports`: Skip reporting on successful proof
  obligations.

* `--target=ARCH`: Pass `ARCH` as the target architecture to LLVM build
  operations.

* `--no-compile`: Assume the input file is an LLVM bitcode module, rather than a
  C program.

* `--symbolic-fs-root=DIR`: Specify a directory containing the initial contents of
  a symbolic filesystem to use during symbolic execution.  See the Symbolic I/O
  documentation for the format of this directory. [Experimental]

# Environment Variables

The following environment variables are supported:

* `BLDDIR`: Specify the directory for writing build files generated from
  the input files.

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

# Symbolic I/O [Experimental]

Note that Symbolic I/O is currently experimental.  We expect that the API (both
internal and command line) will change.

`crux-llvm` supports *symbolic* I/O operations via the POSIX `open`, `read`,
`write`, and `close` functions.  These operations are symbolic in the sense that
the contents of files in the symbolic filesystem can be a mix of concrete and
symbolic values.  The original motivation of the work was to support checking
assertions for programs with configuration files; by supporting symbolic file
contents, `crux-llvm` can check entire families of configuration at once.

## Symbolic Filesystem Contents

The `--symbolic-fs-root` option (and corresponding configuration file option)
enable users to specify the initial contents of the symbolic filesystem.  The
directory pointed to by this options contains:

* A sub-directory named `root` that contains concrete files that will exist in
  the initial filesystem.  The directory layout within `root` is preserved.  For
  example, a file named `root/etc/fstab` will be mapped to `/etc/fstab` in the
  initial symbolic filesystem.
* An optional file named `stdin`, which contains the standard input of the program.
* A manifest named `system-manifest.json` that describes the contents of symbolic files.

The manifest maps absolute file paths to specifications of what parts of the
corresponding file are symbolic.  Note that the specification is currently
coarse and only supports fully-symbolic files.  The format of the system
manifest is:

```
{ "symbolicFiles": [<SymFilePair>],
  "useStdout": bool,
  "useStderr": bool
}

SymFilePair := [ FilePath, <SymbolicFileContents> ]

FilePath := string (an absolute file path)

SymbolicFileContents := { "symbolicContentSize": Word64 }

```

If no initial filesystem is specified, `crux-llvm` defaults to an empty standard
input, while allowing output to standard output and standard error.  Note that
if a program attempts to use the symbolic I/O primitives without being backed by
appropriate files (e.g., opening a file that does not exist), the symbolic I/O
backend will simply report that those functions fail in the expected way (i.e.,
returning -1).

## Interaction with Standard I/O

If the program being verified writes to standard output or standard error (via
the POSIX `STDOUT_FILENO` or `STDERR_FILENO` handles, which correspond to file
descriptors 1 and 2), the symbolic I/O backend reflects as much of the output as
it can to the actual standard output and standard error of `crux-llvm`.  Note
that only *concrete* writes are mirrored to the real world; symbolic writes
still take effect in the symbolic files representing standard output and
standard error.

Note that, due to the branching structure of symbolic execution, the same output
may appear more than once if a call to `write` occurs on a symbolic branch.

## Current Limitations

* Filenames must be concrete
* Filenames must be absolute paths (relative paths require additionally modeling the current working directory)
* Many file operations are not yet modeled
* Files can currently only be entirely concrete or entirely symbolic
* The `open` function does not accept a mode (i.e., file permissions are not yet modeled)
* The `open` function accepts flags (but currently ignores them)
* The `open` function cannot create new files that do not exist in the filesystem
* The special handling of `printf` does not yet interact with the symbolic standard output file descriptor

It is intended that the symbolic I/O facility will be extended over time to
support more operations.

Also note that the order in which file descriptor numbers are handed out to
client code can be subtly different than in the real program. In particular, on
a symbolic branch where both branches open a new file, the two branches will get
sequential file descriptors. In contrast, the real program would allocate the
same file descriptor to both (as only one branch would be taken).

# Acknowledgements

Crux is partly based upon work supported by the Defense Advanced
Research Projects Agency (DARPA) under Contract No. N66001-18-C-4011.
Any opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily reflect
the views of the Defense Advanced Research Projects Agency (DARPA).
