# Behavior tests

This test suite contains standalone C programs. The test harness:

- compiles each program to both a binary and LLVM bitcode (and LLVM IR),
- runs the binary natively,
- runs the LLVM bitcode inside Crucible,
- asserts that the output from both the binary and the simulator match,
- and uses [Oughta] to verify both program output and LLVM assembly structure.

[Oughta]: (https://github.com/GaloisInc/oughta)

These tests should be used when you want to test the fidelity of Crucible-LLVM's
concrete semantics against an oracle (i.e., concrete execution). This is
especially handy for testing overrides that are pure functions, such as
`strcpy`.

- If you want to use symbolic data or test Crucible-LLVM's capacity to catch
  undefined behavior, you should use the Crucible-LLVM-CLI or Crux-LLVM test
  suites instead.
- If you want to test the UX of Crucible-LLVM-CLI or Crux-LLVM (e.g., error
  messages), use those test suites instead.
- If you want to test the behavior of particular functions in Crucible-LLVM,
  consider writing unit or property tests instead.

In addition to hand-written tests containing expected output, we have a variety
of tests from the GCC C "torture" test suite under `gcc-c-torture/`. These files
are GPL-licensed (see that directory for the complete `LICENSE` file). Rather
than printing output, these tests `abort()` on failure, which is treated as a
failure by the test harness.

## Test structure

Each test is a standalone C program. A test must have a `main` function with
one of three possible argument signatures:

- `main(void)`: no arguments
- `main(int argc, char* argv[])`: standard arguments
- `main()`: technically, variadic arguments

The tests should use `printf` to produce meaningful output that
captures the semantics under test. They must use `printf` in a way
that Crucible-LLVM supports (see "Printf accuracy" in [the limitations
doc](../../doc/limitations.md)).

The tests have a timeout of 5s, but they should generally complete in under 1s
for the sake of a reasonably snappy test-suite and CI.

The tests use [Oughta] to verify both program output and LLVM assembly
structure. Oughta provides a DSL for checking patterns in output.

### Output checks

Use `///` comments with Oughta DSL to verify program output:

- `/// checkln "text"` - Check for literal string followed by newline
- `/// check "text"` - Check for literal string (no newline required)

See the Oughta documentation for further information.

Each test needs at least one output check.

### LLVM IR checks

Use `//-` comments with Oughta DSL to verify LLVM IR structure. This is mainly
to ensure that calls are not optimized away by the compiler. Tests should use
`argc` to ensure that the compiler can't compile away calls to any overrides
under test. The test harness guarantees that `argc` is always 1. Use `llvm-dis`
to disassemble the bitcode to ensure it has the structure you want. See the
example below (or the existing tests) for how to do this.

Each test needs at least one LLVM IR check.

### Example

```c
#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;
    char src[6] = "hello";
    char dst[6] = "XXXXX";

    memcpy(&dst[zero], &src[zero], zero);
    //- check "call"
    //- check "@memcpy"
    printf("memcpy zero-length: %c\n", dst[zero]);
    /// checkln "memcpy zero-length: X"

    memcpy(&dst[zero], &src[zero], one);
    //- check "call"
    //- check "@memcpy"
    printf("memcpy single byte: %c\n", dst[zero]);
    /// checkln "memcpy single byte: h"
}
```
