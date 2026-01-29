# Behavior tests

This test suite contains standalone C programs. The test harness:

- compiles each program to both a binary and LLVM bitcode,
- runs the binary natively,
- runs the LLVM bitcode inside Crucible,
- extracts expected output from specially-formatted comments in the C code (see
  below),
- and asserts that the output from both the binary and the simulator match the
  expected output.

These tests should be used when you want to test the fidelity of Crucible-LLVM's
concrete semantics against an oracle (i.e., concrete execution). This is
especially handy for testing overrides that are pure functions, such as
`strcpy`.

- If you want to use symbolic data or test Crucible-LLVM's capacity to catch
  undefined behavior, you should use the Crucible-LLVM-CLI or Crux-LLVM test
  suites instead.
- If you want to test the UX of Crucible-LLVM-CLI or Crux-LLVM (e.g., error
  messages), use those test suites intead.
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
doc](../../doc/limitations.md)). The tests embed the expected output in comments
starting with `/// `. Generally speaking, these comments closely follow the
`printf` invocation that produces the output.

**WARNING**: The tests should use `argc` to ensure that the compiler can't
compile away calls to any overrides under test. Use `llvm-dis` to disassemble
the bitcode to ensure it has the structure you want.

The tests have a timeout of 5s, but they should generally complete in under 1s
for the sake of a reasonably snappy test-suite and CI.

### Example

```c
#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = argc - 1;
    char src[6] = "hello";
    char dst[6] = "XXXXX";

    memcpy(&dst[zero], &src[zero], zero);
    printf("memcpy zero-length: %c\n", dst[zero]);
    /// memcpy zero-length: X

    memcpy(&dst[zero], &src[zero], one);
    printf("memcpy single byte: %c\n", dst[zero]);
    /// memcpy single byte: h
}
```
