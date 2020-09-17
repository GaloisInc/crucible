# Test Suite

This directory contains an executable and test files for testing the
`crux-mir` library. It requires the
[`mir-json`](https://github.com/GaloisInc/mir-json) executable in your
path, so make sure you have it installed.

## Concrete Oracle Tests

These tests use the Rust compiler as an oracle to provide evidence
that terms have been translated accurately. In `conc_eval` and any of
its subdirectories, all Rust source files are turned into test
cases. They have the form:

```rust
fn f(x: $argT) -> $bodyT {
    $body
}

const ARG: $argT = $arg;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
```

Each test case defines a function `f` with a single argument of some
type `$argT`, along with a constant `ARG` of that same type. The
`main` function applies `f` to `ARG` and prints the result. Since the
MIR to Crucible translation cannot currently handle the traits used
for `println!`, the inclusion of `main` is controlled by a `cfg` flag.

When each test case (e.g., `example_test`) runs, we:

1. Compile and run the program with `rustc example_test.rs --cfg
   with_main`, capturing its output
1. Generate MIR JSON from the program with `mir-json example_test.rs
   --crate-type lib` (note that we omit the `with_main` flag to avoid
   analyzing the `println!`)
1. Load the MIR JSON and extract terms for `f` and `ARG`
1. Construct and typecheck a term `app` applying `f` to `ARG` in order to
   determine the result type
1. Parse the output of the oracle program and construct a
   corresponding term `oracle` of the result type
1. Construct and concretely evaluate a term comparing `app` and
   `oracle` for equality
