# UC-Crux-LLVM

UC-Crux-LLVM is a tool for under-constrained symbolic execution of C programs.
It can be used to find undefined behavior and failing assertions, or for simple
functions, to formally verify the absence of such behaviors.

**UC-Crux-LLVM is still in development.**

## Demo

<!-- NOTE(lb) These programs are in the test suite as double_free.c and not_double_free.c --->

<!-- TODO(lb) The printouts from the tool leave a lot to be desired here... --->

`uc-crux-llvm` can use symbolic execution to find the potential double-free in this program:
```c
#include <stdlib.h>
void double_free(int* ptr, int x) {
  if (x % 2 == 0) {
    free(ptr);
  }
  if (x % 3 == 0) {
    free(ptr);
  }
}
```
```
$ uc-crux-llvm --entry-points double_free double_free.c
[CLANG] clang "-c" "-DCRUCIBLE" "-emit-llvm" "-g" "-I" "test/programs" "-I" "/some/pathc/includes" "-O1" "-o" "crux-build/double_free.bc" "test/programs/double_free.c"
[Crux] Attempting to prove verification conditions.
[Crux] Attempting to prove verification conditions.
[Crux] Results for double_free
[Crux] Found likely bugs:
Pointer freed twice
```
That's not too impressive, a simple linter might be able to find that bug. However, since `uc-crux-llvm` uses symbolic execution, it can precisely conclude that the following program _does not_ have a potential double-free (or _any_ other undefined behavior), provided that it's passed a non-null pointer:
```c
#include <stdlib.h>
void not_double_free(int *ptr, int x) {
  if (x % 2 == 0) {
    printf("even!\n"); // needed to prevent Clang from optimizing away the if/else
    free(ptr);
  }
  if ((x + 1) % 2 == 0) {
    free(ptr);
  }
}
```
```
$ uc-crux-llvm --entry-points not_double_free not_double_free.c
[CLANG] clang "-c" "-DCRUCIBLE" "-emit-llvm" "-g" "-I" "test/programs" "-I" "/some/path/c-src/includes" "-O1" "-o" "crux-build/not_double_free.bc" "test/programs/not_double_free.c"
even!
[Crux] Attempting to prove verification conditions.
even!
[Crux] Results for not_double_free
[Crux] Function is safe if deduced preconditions are met:
Arguments:
  A pointer to uninitialized space for 1 elements: 
  An integer:
```
While the examples here have very simple inputs, `uc-crux-llvm` is capable of synthesizing much richer inputs, including nested and recursive structs, pointers, floats, and more.

## How It Works

![Architecture of UC-Crux-LLVM](doc/uc-crux-llvm.svg)

Once a target function has been selected (either by the user or in [Exploratory
Mode](#Exploratory-Mode)), `uc-crux-llvm` will generate the smallest possible
fully symbolic input for that function based on its type signature.
`uc-crux-llvm` will symbolically execute the function on this input, and
iteratively expand it:

- If the symbolic execution succeeded with no safety condition violations,
  it will increase the input depth (up to the user-specified bound) and execute
  it again.

- If some safety conditions were (potentially) violated, the `uc-crux-llvm` will
  examine the error, and either:

  - report it (and optionally continue executing to find other problems), or
  - use heuristics to decide that the error was likely a false positive (i.e.,
    due to a unsatisfied precondition, such as an uninitialized global
    variable). The tool may then use further heuristics to generate inputs or a
    program state/memory layout that satisfies the precondition, such as

    - Allocating memory to back previously unmapped pointers in arguments
    - Expanding the sizes of allocations
    - Initializing global variables

This approach is fairly different from UC-KLEE, which uses "lazy
initialization", i.e., allocating memory *as it's used* by the program.

## Building

### Prerequisites

Before running `uc-crux-llvm`, you'll need to install the following software:

* GHC and `cabal`, preferably using `ghcup`:
  <https://www.haskell.org/ghcup/>

* The Yices SMT solver: <http://yices.csl.sri.com/>

* The Z3 SMT solver: <https://github.com/Z3Prover/z3/releases>

* The Clang compiler: <http://releases.llvm.org/download.html>

We recommend Yices 2.6.x, and Z3 4.8.x. Technically, only one of Yices or Z3 is
required, and CVC4 will work, as well. However, in practice, having both tends
to be convenient. Finally, LLVM versions from 3.6 through 10 are likely to work
well, and any failures with versions in that range should be considered
[bugs](https://github.com/GaloisInc/crucible/issues).

### Building

The `uc-crux-llvm` tool can be built by doing the following:

* Clone the enclosing `crucible` repository:

        git clone https://github.com/GaloisInc/crucible.git

* Change to the `uc-crux-llvm` directory and run the build script:

        cd crucible/uc-crux-llvm
        cabal v2-build

This will compile `uc-crux-llvm` and supporting libraries such that they can be
executed with `cabal v2-run`. To install the binaries in the standard Cabal
binary path, run the following:

        cabal v2-install exe:uc-crux-llvm --overwrite-policy=always

You can also use the `--installdir` flag to install binaries in a different
location.

## Usage

### Targeted Mode

To run `uc-crux-llvm` on a few specific functions, use the `--entry-points` flag:
```
$ uc-crux-llvm --entry-points deref_arg_const_index test/programs/deref_arg_const_index.c
[CLANG] clang "-c" "-DCRUCIBLE" "-emit-llvm" "-g" "-I" "test/programs" "-I" "/some-path/c-src/includes" "-O1" "-o" "crux-build/deref_arg_const_index.bc" "test/programs/deref_arg_const_index.c"
[Crux] Attempting to prove verification conditions.
[Crux] Attempting to prove verification conditions.
[Crux] Results for deref_arg_const_index
[Crux] Function is safe if deduced preconditions are met:
Arguments:
  A pointer to initialized space for 25 elements:
```
For context, the `deref_arg_const_index` function looks like this:
```c
int deref_arg_const_index(int *ptr) { return ptr[24]; }
```
To understand what the tool is checking, try increasing the verbosity with `-v 2`.

### Exploratory Mode

In addition to exploring a few particular functions, `uc-crux-llvm` has an
"exploratory" mode that will attempt to find bugs in (or prove safe) arbitrary
functions in an LLVM program.

- The `--explore` flag enables this mode.
- The `--explore-budget` flag determines how many functions should be explored.
- The `--no-compile` flag specifies that this program has already been compiled to an LLVM bitcode module.
- The exploratory mode leaves logs with more complete reports at `crux-build/<program name>/<function_name>.summary.log`. By default, it won't re-explore functions that already have such a log. You can force it to revisit functions by passing the `--re-explore` flag.
```
$ uc-crux-llvm --explore-budget 25 --explore --no-compile --re-explore libpng16.a.bc
[Crux] Overall results:
  Unclear result, errors are either false or true positives: 14
  Function is always safe: 2
True positives:
Missing preconditions:
  `free` called on an unallocated pointer in argument: 1
  `free` called on pointer with nonzero offset in argument: 1
  Write to an unmapped pointer in argument: 6
  Read from an uninitialized pointer in argument: 1
  Read from an uninitialized pointer calculated from a pointer in argument: 23
  Addition of a constant offset to a pointer in argument: 21
Unimplemented features:
  Arrays in globals or arguments: 9
Uncertain results:
  Unclassified errors: 65
    Unfixable errors:
    Unfixed errors:
  Missing annotations: 1
  Symbolically failing assertions: 1
```

## Roadmap

## Command-line Interface

### Milestone 1: Operating on Realistic Code

- [x] Real error handling
  - [x] Support testing that a given feature is unimplemented
  - [x] Handle unimplemented cases in these areas:
    - [x] Input generation
    - [x] Constraining inputs
  - [x] Report/test any unclassified failures
  - [x] Panic on redundant constraints
- [x] An acceptance test suite (that also tests for e.g., graceful failure on unimplememented features)
- [ ] Support for many types of arguments to functions
  - [x] Integers (bitvectors)
  - [x] Pointers
  - [x] Structs
  - [x] Floats
  - [ ] Arrays
- [x] Increase argument "depth" until saturation or a bound is reached
- [ ] Develop heuristics for more types of errors
  - [x] Missing precondition: Unallocated, uninitialized, or insufficiently aligned pointer inside argument
  - [x] True positive: Concretely failing user assertions
  - [ ] True positive heuristics for out-of-bounds reads/writes
  - [x] True positive: double free
  - [x] Reads from pointer expressions involving input pointers
  - [x] Writes to pointer expressions involving input pointers
  - [ ] Signed wrap with integers from arguments
    - [x] Addition
    - [x] Subtraction
    - [ ] Multiplication
  - [ ] Division by zero
  - [ ] Mod by zero

### Milestone 2: Publishable

- [x] Rename package to UC-Crux-LLVM
- [x] Revise CLI (make a `Crux.Config`)
- [ ] Print concretized inputs that make errors occur
- [x] README
  - [x] With "outer loop" flowchart
  - [ ] With CLI docs
  - [ ] With demo at the top: double free

### Milestone 3: Finding Bugs in Large Codebases

- Goal: Low false positives
  - [ ] Flags for (not) reporting each category of uncertain errors, like unclassified errors or symbolically failing user assertions
  - [ ] Setting to only report true positives found by a specific list of heuristics
- Goal: Usable UX
  - [x] Multi-function target mode that doesn't recompile/re-parse bitcode
  - [x] "Exploration" mode (not targeting a single function)
    - [x] Per-function reports saved to disk
    - [x] Report # of unclassified errors
    - [x] Report # of classified, but un-actionable false positives
    - [x] Report # of classified, but not-yet actionable false positives
    - [x] Report # of times each false positive and true positive heuristic was used
    - [ ] Report # times each unimplemented feature of UC-Crux was hit (to support prioritization)
    - [ ] Report unimplemented overrides
    - [ ] Catch and report panics and unimplemented behaviors
    - [x] Good overall "summary" report
- Goal: Handle even more kinds of behaviors
  - [ ] Support generating allocations for reads/writes through pointers appearing in globals
  - [x] Support generating pointer arguments that are treated as arrays
- Goal: Robustness to unforeseen conditions
  - [ ] Setting to ignore or raise errors that have no applicable heuristics

### Milestone 4: The Dream Achieved

- [ ] Optionally skipping missing functions
- [ ] Way more heuristics
  - [ ] True positive: Signed wrap when both arguments are concrete
- [ ] Generate runnable counter-examples in C
- [ ] Relational preconditions between arguments and globals
  - [ ] `int` field is the length of a pointer field
- [ ] Support generating function pointers
- [ ] Support/suggest user annotations on data structures, in functions
