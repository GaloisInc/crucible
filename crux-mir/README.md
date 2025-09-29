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

There are two different ways to set up `mir-json`: either by downloading the binaries from GitHub Actions (see the [Download `mir-json` binaries](#download-mir-json-binaries) section) or by building it from source (see the [Build `mir-json` from source](#build-mir-json-from-source) section).

### Download `mir-json` binaries

To download the latest version of `mir-json`, go to the [mir-json CI workflows](https://github.com/GaloisInc/mir-json/actions/workflows/ci.yml) page. Select the latest build from the `master` branch and scroll down the page, until you find and download the desired binary release (`mir-json-macos...` or `mir-json-ubuntu...`). Unzip the downloaded archive and add it to your path.

The binary release comes with precompiled `rlibs`, so don't forget to set `CRUX_RUST_LIBRARY_PATH` variable pointing to the `rlibs` subfolder of the unzipped archive. Adding `export CRUX_RUST_LIBRARY_PATH=...` to your shell configuration is recommended.


### Build `mir-json` from source

`crux-mir` uses several submodules, so make sure they're initialized:

    $ git submodule update --init

Next, navigate to the `crucible/dependencies/mir-json` directory. Install
`mir-json`, translate its standard libraries, and define the
`CRUX_RUST_LIBRARY_PATH` environment variable according to the instructions in
[the `mir-json` README][mir-json-readme].

Currently, `crux-mir` supports [version
4](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#4) of
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


## Setup: `crux-mir`


There are two different ways to set up `crux-mir`: either by downloading the binaries from GitHub Actions (see the [Download `crux-mir` binaries](#download-crux-mir-binaries) section) or by building it from source (see the [Build `crux-mir` from source](#build-crux-mir-from-source) section).


### Download `crux-mir` binaries

`crux-mir` comes with nightly builds and stable [binary releases](https://github.com/GaloisInc/crucible/releases). If you want to install the nightly build, do the following:

* Go to the [crux-mir action](https://github.com/GaloisInc/crucible/actions/workflows/crux-mir-build.yml) page
* Select the last build from `master` and scroll down the page, until you find and download the desired binary release (`crux-mir-macos...` or `crux-mir-ubuntu...`)
* Unzip the downloaded archive and add it to your path


### Build `crux-mir` from source

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
Rust crate.  See [`examples/example-1/lib.rs`](examples/example-1/lib.rs) or the files in
[`test/symb_eval/`](test/symb_eval) for examples of creating symbolic values
and asserting properties about them.

### Running on a Cargo project

Set the `CRUX_RUST_LIBRARY_PATH` environment variable to the path to the
translated libraries:

    $ export CRUX_RUST_LIBRARY_PATH=<mir-json checkout>/rlibs

In the directory of a Cargo project (such as the [find-first-set
example](examples/example-1)), run the project's symbolic tests:

    $ cargo crux-test --lib

`cargo-crux-test` (part of `mir-json`) will translate the code to MIR, then
invoke `crux-mir` to symbolically simulate the test cases.

### Running on a single file

To compile and test a single Rust program:

    $ cabal exec -- crux-mir test/conc_eval/prim/add1.rs

(Should print 2.)

### Code coverage

`crux-mir` has a code coverage tool that reports branches where only one side or the other was explored during symbolic execution. Note that due to how `mir-json` works, this will only report issues in functions that are called at least once from a `#[crux::test]` entrypoint. If you have dead code (i.e., functions that are never called by any entrypoint), then `mir-json` will discard the dead functions, which means that they won't be mentioned at all in the coverage output. Code coverage currently does not report the percentage of the coverage, only lists the paths that are not covered.

* Clone this directory with `git clone https://github.com/GaloisInc/crucible.git` as we will need the `report-coverage` utility tool
* In your crate run:
  ```
  $ cargo crux-test --lib --  --branch-coverage --path-sat --output-directory test-coverage
  ```
* In your crate, run the following command, pointing it towards the `report-coverage` folder in `crucible` directory, which contains the coverage script. You will need to point to a directory in the `test-coverage` folder that contains a function's coverage report data (`report_data.js`):
  ```
  $ cargo run --manifest-path $PATH_TO_CRUCIBLE_REPO/report-coverage/Cargo.toml -- test-coverage/$YOUR_CRATE_NAME$/62f2dedb\:\:f\[0\]#aaa/report_data.js
  ```

  Note that the `62f2dedb` part of this path will likely be different on your machine due to how `mir-json` works. And `$YOUR_CRATE_NAME` is the `name` specified in the crate's `Cargo.toml` file.  The `#a` suffix is a tag derived from the crate and function name to avoid name collisions on case insensitive file systems.

  It is also possible to run `report-coverage` with multiple input files, in which case you will
  get the combined coverge from all tests.  For example:
  ```
  find ./test-coverage -name 'report_data.js' | xargs cargo run --manifest-path $COV_REP --
  ```
  where `COV_REP` is the path to `report-coverage` as above.

* This will report all paths not covered, for example:
  ```
  warning: branch condition never has value false
     ┌─ lib.rs:43:13
     │
  43 │     assert!(a == b);
     │             ^^^^^^

  ✅ 100% example_1/ffs_fast[0]: 10/10
  ✅ 100% example_1/ffs_ref[0]: 4/4
  🚧  50% example_1/test_ffs_correct[0]: 1/2
  ❌  0% example_1/never_called_func[0]: 0/0
  ```
  In addition to warnings about uncovered paths, we generate statistics about
  the coverage for each function.   A green checkmark (✅) indicates that a
  function was called during symbolic execution and *all* paths were covered, while a red cross (❌) indicates that a function was not visited at all. A construction sign (🚧) indicates a function that was called, but not all branches were covered.
  For each function we also report how many of the alternatives of all branches were visited, which is also summarized as a percentage.

* To limit the coverage only to the code in your crate, use `--filter` to point the tool to the file you want to analyze. Then you get a more condensed output, for example:
  ```
  $ cargo run --manifest-path $PATH_TO_CRUCIBLE_REPO/report-coverage/Cargo.toml -- --filter test.rs test-coverage/test/62f2dedb\:\:f\[0\]#a/report_data.js
  warning: branch condition never has value false
    ┌─ test.rs:2:8
    │
  2 │     if b {
    │        ^
  ```

### Symbolic profiling

`crux-mir` support symbolic profiling, i.e., displaying profiling information for symbolic execution. This information can be useful to see if a particular proof or test is taking an outsized amount of time, and to understand the execution profile. `crux-mir` uses [`sympro-ui`](https://github.com/GaloisInc/sympro-ui) for visualization of the traces.

In order to record a profiling trace, run `crux-mir` with the arguments `--branch-coverage --path-sat --output-directory test-coverage --profile-crucible --profile-solver --skip-report` to generate the necessary profiling events. The full command would be:

```
$ cargo crux-test --lib -- --branch-coverage --path-sat --output-directory test-coverage --profile-crucible --profile-solver --skip-report
```

This will generate a `report_data.js` file that can be fed into the [`sympro-ui`](https://github.com/GaloisInc/sympro-ui) tool. An example of a more complicated `crux-mir` proof for a SHA2 implementation is shown below:

![symbolic profile](./crux-mir-symbolic-profiling.png)

`_start` is a dummy name that Crucible assigns to the entrypoint to symbolic execution. First, `crux-mir` performs symbolic execution and generates a number of proof goals, generally corresponding to the `crux::test` proofs.

The second part of the `crux-mir` invocation, under the `<Prove Goals>` label, is attempting to discharge the proof goals to an SMT solver. Because the SMT solvers are external subprocesses, `crux-mir` does not have much profiling information besides the total duration.

## Examples

The [examples/](examples/) directory in this repository contains a number of examples with concrete and symbolic tests.
Have a look at [examples/README.md](./examples/README.md) to learn more about different ways to use `crux-mir`.

A fork of the curve25519-dalek library with symbolic tests for the `Scalar52`
type is available [here][dalek-fork].  This is the code that appears in the
[`crux-mir` demo video][video].

[dalek-fork]: https://github.com/GaloisInc/curve25519-dalek


## Test suite

To run `crux-mir`'s test suite:

    $ cabal test

You need to have built and installed the mir-json tool such that it can be found
on your $PATH. You also need translated libraries for the Rust target
architecture you're testing on. See the [Setup: `mir-json`](#setup-mir-json)
section above for more details.

### Expected Failures

Some tests are not yet expected to succeed, as crux-mir is still under
development. These tests are marked accordingly, so that the entire
test suite is still expected to pass.

Files that are not yet expected to work correctly begin with `// FAIL: ` and
a brief comment describing the reason for the expected failure.


## Limitations & How-to


### Unsafe code

`crux-mir` does not support reasoning about certain types of unsafe code.  Many
functions in the standard library rely on unsafe code; we have reimplemented
some of these in terms of safe code or custom `crux-mir` intrinsics, but many
unsupported functions still remain.  Test cases that call into unsupported code
will produce assertion failures with messages like `don't know how to call
core::intrinsics::transmute`.


### References & function pointers

Currently, `crux-mir` also has trouble supporting references and function
pointers in constant expressions and static initializers.


### Symbolic size arrays

`crux-mir` does support vectors (and data structures) with a symbolic capacity if an upper bound on the size is provided. Truly unbounded sizes are not supported. For example, a `Vec` with *symbolic* length but *fixed* capacity can be used as follows:

```Rust
let mut v = Vec::with_capacity(8);
for _ in 0 .. usize::symbolic_where("n", |n| n <= 8) {
    v.push(i32::symbolic("x"));
}
```


### Don't know how to call...

If you get a translation error and ` Don't know how to call...` message (an example is below), that usually means that your code contains a compiler intrinsic that `crucible-mir` doesn't know how to simulate. Often times, this can be fixed by adding a custom override for the intrinsic. In such case, we encourage you to look through the [existing issues](https://github.com/GaloisInc/crucible/issues) if such missing case was reported already, and if not, open a new issue.

The error will look similar to this:

```
[Crux]   Translation error in subtle/81045fbd::black_box[0]::_inst2efc261c2cb07b6c[0]: callExp: Don't know how to call core/c7248340::intrinsics[0]::volatile_load[0]::_inst2efc261c2cb07b6c[0]
```

Similarly, if you see a Haskell error trace in the output, you have likely discovered a bug.


### Loop-unrolling

If your code contains loops, the default invocation `cargo crux-mir --lib` might be very slow. If that is the case, add `--path-sat` argument. Then each time around the loop, `crux-mir` will check with the solver whether it should keep unrolling or not. The full command is:

```
$ cargo crux-test --lib -- --path-sat
```


### Print counterexamples

When your test fails, it is often useful to get a concrete counterexample to better understand which input causes the failure. You can use the `-m` argument to print the counterexample:

```
$ cargo crux-test --lib -- -m
...
---- kinds_of_failure/c15b5012::overflow_quicksort[0]::crux_test[0]::midpoint_overflow[0] counterexamples ----
[Crux] Found counterexample for verification goal
[Crux]   src/overflow_quicksort.rs:31:27: 31:34: error: in kinds_of_failure/c15b5012::overflow_quicksort[0]::crux_test[0]::midpoint_overflow[0]
[Crux]   attempt to compute `copy _1 + copy _2`, which would overflow
Model:
[{"name": "a","loc": null,"val": "-0x58cf1802","bits": "32"},{"name": "b","loc": null,"val": "0x58cf1803","bits": "32"}]
```

The model shows the name of variable, as well as its concrete value.

In addition to `-m` (which can be hard to interpret if you have multiple symbolic variables with the same name), you can use the `crucible_assert!()` macro. For example `crucible_assert!(x == y, "expected x == y, but got x = {} and y = {}", x, y);` will print some concrete values of `x` and `y`.

### Constraining symbolic values

The code below is equivalent, use either construct as appropriate:

```Rust
// A
let x = u8::symbolic_where("x", |x| x < 3);

// B
let x = u8::symbolic("x");
crucible_assume!(x < 3);

// C
let x = u8::symbolic("x");
if !(x < 3) { crucible_assume_unreachable!(); }
```


### Where is the source code for the crucible crate?

You are probably looking for [https://github.com/GaloisInc/mir-json/tree/master/libs/crucible](https://github.com/GaloisInc/mir-json/tree/master/libs/crucible).


### Where is the documentation for the crucible crate?

The documentation for the `crucible` crate can be built locally, as described in [`mir-json`'s README](https://github.com/GaloisInc/mir-json#readme)


### Implement `Symbolic` trait for a custom type

To be able to call `MyType::symbolic()` you need to implement the [`Symbolic`](https://github.com/GaloisInc/mir-json/blob/master/libs/crucible/symbolic.rs#L1) trait. For example, for a simple `enum` the implementation can be as follows:

```Rust
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Rating {
    One,
    Two,
    Three,
}

impl Symbolic for Rating {
    fn symbolic(desc: &'static str) -> Self {
        let val = u8::symbolic_where(desc, |&x| x <= 3);
        match val {
            1 => Rating::One,
            2 => Rating::Two,
            3 => Rating::Three,
            _ => crucible_assume_unreachable!(),
        }
    }
}
```

In this example `crucible_assume_unreachable!()` is a symbolic equivalent of `unreachable!()` macro.
