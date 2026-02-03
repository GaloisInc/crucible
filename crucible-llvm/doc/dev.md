# Crucible-LLVM developer documentation

## Adding an override

To add an override to Crucible-LLVM:

- Carefully read the manpage (`man 3 FUN`). Pay special attention to mentions
  of undefined behavior. If the manpage mentions the possibility undefined
  behavior, the override must assert that it does not occur. For example,
  the behavior of `strcpy` is undefined if the strings overlap, and the
  corresponding override asserts that this does not occur.
- Add the declaration and definition to `Intrinsics.Libc` or `Intrinsics.LLVM`.
- Add the declaration to the appropriate list, e.g., `libc_overrides` if it
  appears in libc or `basic_llvm_overrides` if it is an LLVM override (usually
  starting with `@llvm.*`).
- Add tests.
  - Consider adding a test in `crucible-llvm/test/behavior`. See the README
    there for further discussion. These tests should generally be preferred
    for testing non-UB functionality, as they confirm that the override behaves
    faithfully to a real implementation.
  - Consider adding a test in `crucible-llvm-cli/test-data/simulate`. See
    `strdup.cbl` for an example. If the override can exhibit undefined behavior,
    that should be covered by a test here.
- Try running the test manually with: `cd crucible-cli && cabal run -- simulate
  test-data/simulate/TEST.cbl`. Ensure that the output is what you expect.
- Create the golden output file at `test-data/simulate/TEST.out` with `cd
  crucible-cli && cabal run test:crucible-llvm-cli-tests --`. Double-check the
  output.
- If the override has any substantial limitations that make it less general than
  actual C implementations (e.g., certain arguments must be concrete, it always
  reports failure, etc.), note them in `doc/limitations.md`.
- Note the addition of the override in `CHANGELOG.md`, e.g., "Add override for
  `FUN`.".
