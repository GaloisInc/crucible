# crux-mir tutorial

This tutorial is intended for engineers with *some* understanding of formal methods, rather than for formal methods experts. After reading through the tutorial, you should be able to write symbolic tests for your Rust code, and understand the results provided by `crux-mir`. This tutorial is [learning oriented](https://docs.divio.com/documentation-system/), if you need a quick reference for fixing problems, we recommend the [Limitations & How-to](https://github.com/GaloisInc/crucible/blob/master/crux-mir/README.md) section in the [crux-mir README.md](https://github.com/GaloisInc/crucible/blob/master/crux-mir/README.md)

The `crux-mir` tool is geared towards compiling and testing a single, standalone Rust file. `mir-json` also offers a `cargo` subcommand, `cargo crux-test`, which generalizes `crux-mir` to allow compiling and testing a complete Cargo project. While we will be using `cargo crux-test` below to compile all of the examples, we will use the terms "`crux-mir`" and "`crux-test`" interchangeably to describe the underlying machinery.

## Example 1: Find First Set

This example implements the [Find First Set](https://en.wikipedia.org/wiki/Find_first_set) algorithm and uses `crux-mir` to prove equivalence between the reference implementation and the fast implementation.


Note that you don't need to create a new module, `cfg_attr` lets you specify individual functions that are visible only to `crux-test`:

```Rust
#[cfg_attr(crux, crux::test)]
fn test_ffs_correct() {
    let x = u32::symbolic("x");
    let a = ffs_ref(x);
    let b = ffs_fast(x);
    assert!(a == b);
}
```

Run the test with:

```
$ cd example-1
$ cargo crux-mir --lib
```

We expect to see that our test is passing, and the output will be similar to this:

```
Finished `test` profile [unoptimized + debuginfo] target(s) in 0.20s
Running unittests lib.rs (target/aarch64-apple-darwin/debug/deps/ffs-eede706fc7fe3aba)
test ffs/00e289e7::test_ffs_correct[0]: [Crux] Attempting to prove verification conditions.
ok

[Crux-MIR] ---- FINAL RESULTS ----
[Crux] Goal status:
[Crux]   Total: 2
[Crux]   Proved: 2
[Crux]   Disproved: 0
[Crux]   Incomplete: 0
[Crux]   Unknown: 0
[Crux] Overall status: Valid.
```

## Example 2: Failing corner case

**NOTE:** this example was adapted from the [Kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html).

In this example, we have hidden a failing corner case that triggers `panic!`. A regular `proptest` which uses random inputs will most likely not discover this case, so running `cargo test` will pass.

However, when we write a symbolic test with `x` being a `u32::symbolic` variable, `crux-mir` will discover the edge case. Note that in this case we are defining a `crux_test` module. This is suitable when we expect having more than one symbolic test, or when we need to define helper functions:

```Rust
#[cfg(crux)]
mod crux_test {
    use super::*;
    extern crate crucible;
    use self::crucible::*;

    #[crux::test]
    fn check_estimate_size() {
        let x: u32 = u32::symbolic("x");
        estimate_size(x);
    }
}
```

Run the test with:

```
$ cd example-2
$ cargo crux-test --lib
```

The output will be something like:

```
[Crux] Found counterexample for verification goal
[Crux]   src/lib.rs:16:29: 16:47: error: in first_steps_v1/0159ee56::estimate_size[0]
...
[Crux-MIR] ---- FINAL RESULTS ----
[Crux] Goal status:
[Crux]   Total: 2
[Crux]   Proved: 0
[Crux]   Disproved: 2
[Crux]   Incomplete: 0
[Crux]   Unknown: 0
[Crux] Overall status: Invalid.
```

Looking at the error message, we see that the error points to our failing corner case! Can we tell which exact value triggers this error? Yes! Add `-m` argument to the `crux-test` invocation, which will print the counterexample:

```
$ cargo crux-test --lib -- -m
```

And the output will contain the model value:

```
Model:
[{"name": "x","loc": null,"val": "0x3ff","bits": "32"}]
```

Note that the variable value is printed in hexadecimal format. `x` is the name of the symbolic variable, assigned when creating `u32::symbolic("x")`, and the value `0x3ff` is `1023` in decimal, which neatly matches the condition guards:

```Rust
...
 } else if x < 1024 {
        if x > 1022 {
...
```

## Example 3: Constrain input values

**NOTE:** this example was adapted from the [kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html).

In this example, we have a function that requires the input to be smaller than 4096:

```Rust
fn estimate_size(x: u32) -> u32 {
    assert!(x < 4096);
...
```

In our test suite, we limit the input such that the assertion is not triggered (try running `cargo test`), but when we write our symbolic test and check the function with *all possible values*, we get an error:

```Rust
#[crux::test]
fn will_fail() {
    let x: u32 = u32::symbolic("x");
    let y = estimate_size(x);
}
```

Let's run the `will_fail` test, and because we have more than one test in this example, append `will_fail` at the end of the invocation to filter which tests are run:

```
$ cd example-3
$ cargo crux-test --lib -- -m will_fail
...
---- first_steps_v2/fb96b074::crux_test[0]::will_fail[0] counterexamples ----
[Crux] Found counterexample for verification goal
[Crux]   src/lib.rs:6:5: 6:22 !src/lib.rs:6:5: 6:22: error: in first_steps_v2/fb96b074::estimate_size[0]
[Crux]   panicking::panic, called from first_steps_v2/fb96b074::estimate_size[0]
Model:
[{"name": "x","loc": null,"val": "-0x80000000","bits": "32"}]

[Crux-MIR] ---- FINAL RESULTS ----
[Crux] Goal status:
[Crux]   Total: 1
[Crux]   Proved: 0
[Crux]   Disproved: 1
[Crux]   Incomplete: 0
[Crux]   Unknown: 0
[Crux] Overall status: Invalid.
error: test failed, to rerun pass `--lib`
```

OK, that looks bad - we gave the `estimate_size()` function a really big `u32` number, and it triggered the assertion (which in turn triggers `panic!` and that is what you see in the error message). Fortunately we can make assumptions about the symbolic values with the `crucible_assume!` macro. From the documentation of `crucible_assume!`:

> Assume that a condition holds. `crux-mir` will not consider assignments to the symbolic variables that violate an assumption.

Let's write a new test, and assume that the symbolic value is always less than 4096:

```Rust
#[crux::test]
fn verify_success() {
    let x: u32 = u32::symbolic("x");
    crucible_assume!(x < 4096);
    let y = estimate_size(x);
    assert!(y < 10);
}
```

Let's run the test (this time we want to run only `verify_success`):

```
$ cargo crux-test --lib -- -m verify_success
...
test first_steps_v2/9d5ad719::crux_test[0]::verify_success[0]: [Crux] Attempting to prove verification conditions.
ok

[Crux-MIR] ---- FINAL RESULTS ----
[Crux] Goal status:
[Crux]   Total: 1
[Crux]   Proved: 1
[Crux]   Disproved: 0
[Crux]   Incomplete: 0
[Crux]   Unknown: 0
[Crux] Overall status: Valid.
```

And the test passes! You can use `crucible_assume!` any time you need to place constraints on your symbolic variables.


## Example 4: Loop unwinding

**NOTE:** this example was adapted from the [kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html).

In this case we have code with a simple loop:

```Rust
fn initialize_prefix(length: usize, buffer: &mut [u8]) {
    // Let's just ignore invalid calls
    if length >= buffer.len() {
        return;
    }

    for i in 0..=length {
        buffer[i] = 0;
    }
}
```

and we want to check that the buffer is zero initialized for any length (within a certain limit). Lets write a symbolic test for this:

```Rust
#[crux::test]
fn check_initialize_prefix() {
    const LIMIT: usize = 10;
    let mut buffer: [u8; LIMIT] = [1; LIMIT];

    let length = usize::symbolic("x");
    initialize_prefix(length, &mut buffer);
}
```

Notice we decided to use a relatively small array with only 10 elements. Let's run the test:

```
$ cd example-4
$ cargo crux-test --lib
...
# lot of time passes and the test is still running
```

That looks like we have a test that does not terminate! Should we constraint the size of `length` with `crucible_assume!`? That will not help here, because any value that is larger than `buffer.len()` will lead to the same branch, and `crux-mir` is smart enough to know that. And if you assume that `length` is smaller than `LIMIT`, you are not covering all cases. We could also make `LIMIT` smaller, but 10 is already pretty small.

Fortunately, we have an argument for loop unrolling! Add `--path-sat` to your `crux-mir` invocation. Then each time around the loop, `crux-mir` will check with the solver whether it should keep unrolling or not.

```
$ cargo crux-test --lib -- --path-sat
...
[Crux]   Index out of range for access to slice
[Crux] Found counterexample for verification goal
[Crux]   src/lib.rs:11:9: 11:22: error: in loops_unwinding/b472e3cb::initialize_prefix[0]
[Crux]   vector index out of range: the length is 10

[Crux-MIR] ---- FINAL RESULTS ----
[Crux] Goal status:
[Crux]   Total: 13
[Crux]   Proved: 10
[Crux]   Disproved: 3
[Crux]   Incomplete: 0
[Crux]   Unknown: 0
[Crux] Overall status: Invalid.
```

Now we got an answer - and it looks like we have a bug in our code. Can you spot it?
We can also ask `crux-mir` to print the counterexample with `-m`:

```
$ cargo crux-test --lib -- --path-sat -m
...
[Crux] Found counterexample for verification goal
[Crux]   src/lib.rs:11:9: 11:22: error: in loops_unwinding/b472e3cb::initialize_prefix[0]
[Crux]   vector index out of range: the length is 10
Model:
[{"name": "x","loc": null,"val": "0xaL","bits": "64"}]
...
```

Remember that `0xa` is 10 in decimal. Once you fix the bug, see how much you can increase the size of the buffer by increasing `const LIMIT` and still get a result within a reasonable time ⌛


## Example 5: Integer overflow

**NOTE:** this example was adapted from the [kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html).

In this example, we have a function that calculates the average of two values:

```Rust
fn find_midpoint(low: u32, high: u32) -> u32 {
    return (low + high) / 2;
}
```

We also have a simple symbolic test that tests the function with all possible input values:

```Rust
#[crux::test]
fn midpoint_overflow() {
    let a = u32::symbolic("a");
    let b = u32::symbolic("b");
    find_midpoint(a, b);
}
```

When we run the test, we get an overflow error:

```
$ cd example-5
$ cargo crux-test --lib -- midpoint_overflow
...
---- kinds_of_failure/a61f4978::overflow_quicksort[0]::crux_test[0]::midpoint_overflow[0] counterexamples ----
[Crux] Found counterexample for verification goal
[Crux]   src/overflow_quicksort.rs:5:12: 5:24: error: in kinds_of_failure/a61f4978::overflow_quicksort[0]::find_midpoint[0]
[Crux]   attempt to compute `copy _1 + copy _2`, which would overflow
...
```

There are several ways to fix this, but lets say we want to see what value caused the overflow so we add `-m` to the invocation:

```
$ cargo crux-test --lib --  -m midpoint_overflow
...
Model:
[{"name": "a","loc": null,"val": "0xa730e7fe","bits": "32"},{"name": "b","loc": null,"val": "0x58cf1803","bits": "32"}]
```

Note that the model representation is a bit hard to read, and might change (see [#1434](https://github.com/GaloisInc/crucible/issues/1434) for details). This shows us two values that when added together overflow `u32`, which is an error. You might get different values (depending on your solver), but they will overflow `u32` when added together.

If you are wondering how to best fix this error, have a look at the [Kani tutorial](https://model-checking.github.io/kani/tutorial-kinds-of-failure.html#exercise-classic-overflow-failure) where this example is adapted from.


## Example 6: Debugging with crucible_assert

**NOTE:** this example was adapted from the [kani tutorial](https://model-checking.github.io/kani/kani-tutorial.html).

In this example, we introduced a subtle mathematical error when accessing array elements. Can you spot it right away?

```Rust
fn get_wrapped(i: usize, a: &[u32]) -> u32 {
    if a.len() == 0 {
        return 0;
    }

    let idx = i % a.len() + 1;
    return a[idx];
}
```

Fortunately we have a symbolic test to help us find it:

```Rust
#[crux::test]
fn bound_check() {
    const LIMIT: usize = 10;
    let size = LIMIT;
    let i = usize::symbolic("i");
    let array: Vec<u32> = vec![1; size];
    get_wrapped(i, &array);
}
```

Note that while we could create a `Vec` with *symbolic* length but *fixed* capacity, rather than a fixed length vector. It would come at a performance cost, and in this example it does not make a difference. However, have a look at the [Limitations & How-to](https://github.com/GaloisInc/crucible/blob/master/crux-mir/README.md) section in the [crux-mir README.md](https://github.com/GaloisInc/crucible/blob/master/crux-mir/README.md) for an example of how to create a vector with *symbolic* length.

Let's run this example, and because we expect to find a bug there, use `-m` to show the counterexample right away:

```
$ cd example-6
$ cargo crux-test --lib -- -m
...
---- kinds_of_failure/3c6b0fc0::bounds_check[0]::crux_test[0]::bound_check[0] counterexamples ----
[Crux] Found counterexample for verification goal
[Crux]   src/bounds_check.rs:12:12: 12:18: error: in kinds_of_failure/3c6b0fc0::bounds_check[0]::get_wrapped[0]
[Crux]   index out of bounds: the length is move _9 but the index is copy _4
Model:
[{"name": "i","loc": null,"val": "-0x3ffffffffffffff9L","bits": "64"}]
[Crux] Found counterexample for verification goal
[Crux]   src/bounds_check.rs:12:12: 12:18: error: in kinds_of_failure/3c6b0fc0::bounds_check[0]::get_wrapped[0]
[Crux]   Index out of range for access to slice
Model:
[{"name": "i","loc": null,"val": "-0x3ffffffffffffff9L","bits": "64"}]
[Crux] Found counterexample for verification goal
[Crux]   src/bounds_check.rs:12:12: 12:18: error: in kinds_of_failure/3c6b0fc0::bounds_check[0]::get_wrapped[0]
[Crux]   Attempted to read uninitialized vector index
Model:
[{"name": "i","loc": null,"val": "-0x6904d3b2322de041L","bits": "64"}]
```

Looks like our index is out of range for the given vector! It also looks like the generated values of the index `i` are not particularly helpful. Let's say we are not really sure which value causes the bug, and would like to know more.

Fortunately we can use `crucible_assert!` macro, which is described as:

> Assert that a condition holds. During symbolic testing, `crux-mir` will search for an assignment to the symbolic variables that violates an assertion.
> 
> This macro works just like the standard `assert!`, but currently produces better error messages.
> 
> If the error message uses string formatting, `crux-mir` will choose an arbitrary concrete counterexample and use its values when formatting the message. For example: `crucible_assert!(x + y == z, "bad arithmetic: {} + {} != {}", x, y, z);` might print a message like bad arithmetic: `1 + 2 != 4`, assuming `x`, `y`, and `z` are symbolic variables that can take on the values 1, 2, and 4..

We can use `crucible_assert!` in both the crux test code and in the source code. In this case we will edit the source code, because we want to know what is the value of `idx` before the out of bounds access is attempted:

```Rust
extern crate crucible;
use self::crucible::*;
fn get_wrapped(i: usize, a: &[u32]) -> u32 {
    if a.len() == 0 {
        return 0;
    }

    let idx = i % a.len() + 1;
    crucible_assert!(idx < a.len(), "idx={}, a.len()={}, i = {}", idx, a.len(), i);
    return a[idx];
}
```

When we run the code, the assertion will print additional debug information:

```
$ cargo crux-test --lib -- bound_check
...
[Crux] Found counterexample for verification goal
[Crux]   ./libs/crucible/lib.rs:48:13: 55:14 !src/bounds_check.rs:12:5: 12:83: error: in kinds_of_failure/acd766e3::bounds_check[0]::get_wrapped[0]
[Crux]   MIR assertion at src/bounds_check.rs:12:5:
[Crux]          idx=10, a.len()=10, i = 089
...
```

Seeing that index `i=89` leads to `idx=9+1=10` which is the same as `a.len()` tells us we are off by one! You can use `crucible_assert!` when debugging complex errors in your code. Just don't forget to remove the `crucible` code when you are done debugging, as it would trigger a compilation error when building the code with `cargo build`.

There is also `crucible_assert_unreachable!` which can be used instead of the `unreachable!` macro.


## Example 7: Crux-mir in CI and changing solvers

A fork of the curve25519-dalek library with symbolic tests for the `Scalar52`
type is available [here](https://github.com/GaloisInc/curve25519-dalek). This is the code that appears in the [`crux-mir` demo video](https://www.youtube.com/watch?v=dCNQFHjgotU). We added a [`prove` CI job](https://github.com/GaloisInc/curve25519-dalek/blob/master/.github/workflows/ci.yml#L59) that shows how to use `crux-mir` in GitHub Actions. Similar approach will work in GitLab CI.

The resulting workflow runs are in the repo's [Actions page](https://github.com/GaloisInc/curve25519-dalek/actions/workflows/ci.yml). Note the actual `crux-mir` invocation is quite simple:

```yml
...
 - name: Run proofs
        run: |
          cargo crux-test --lib -- -s z3
...
```

Note the `-s z3` flag, which tells `crux-mir` to specifically use the `z3` solver (assuming it is installed). In some cases it might be beneficial to use specific solvers, but the details of when are beyond the scope of this tutorial.


## Parting thoughts

Hope you enjoyed the tutorial! If you have questions or run into problems, feel free to open a new issue in [our issue tracker](https://github.com/GaloisInc/crucible/issues).
