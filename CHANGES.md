# Version 0.2-dev

* Major improvements to the Java and LLVM verification infrastructure,
  as described in more detail [here](doc/java-llvm/java-llvm.md):
    * Major refactoring and polish to `java_verify` and `java_symexec`
    * Major refactoring and polish to `llvm_verify` and `llvm_symexec`
    * Fixed soundness bug in `llvm_verify` treatment of heap
      modifications
    * Fixed soundness bug related to `java_assert` and `llvm_assert`
    * Support for branch satisfiability checking to be configured
    * Support for some types of allocation in `java_verify`, enabled
      with `java_allow_alloc`
    * Improved support for LLVM structs (including the `llvm_struct`
      type for `llvm_verify`)
    * Support for non-scalar return values in `java_verify` and
      `java_symexec`
    * Support for using `java_ensure_eq` on fields of return value
    * Access to safety conditions in `java_symexec` and `llvm_symexec`
    * New primitives `llvm_assert_eq` and `java_assert_eq`

* Some changes to the SAWScript language:
    * Conditional expressions including the keywords `if`, `then`, and
      `else`, and the new constants `true` and `false`
    * New `eval_int` and `eval_bool` functions to expose Cryptol bit
      vectors and `Bit` values as `Int` and `Bool` values in SAWScript
    * Pattern matching for tuples
    * Improvements to pretty printing, including: `set_base` and
      `set_ascii` commands to control the formatting of values; a `show`
      function to convert a value to a string without printing it; and
      the ability to use `print` or `show` instead of
      `llvm_browse_module` and `java_browse_class`
    * New built-in functions for processing lists: TODO names

* New proof backends:
    * A new `rme` proof tactic, based on the
      [Reed-Muller Expansion](https://en.wikipedia.org/wiki/Reed%E2%80%93Muller_expansion)
      normal form for propositional formulas. This tactic is
      particularly efficient for dealing with polynomials over Galois
      fields, as used in AES, for instance.

* Linked against the latest Cryptol code, which includes the following
  changes since release 2.3.0:
    * An extended prelude with more Haskell-like functions
    * Better, more portable seeding for `random`
    * Performance improvements for symbolically executing tables of
      constant values
    * Performance improvements for type checking large constants

* Internal improvements:
    * Simplified Cryptol to SAWCore translation
    * Improved performance of Cryptol to SAWCore translation for
      recursive functions
    * Updated bitcode parser to support some of the changes in LLVM 3.7
    * Many bug fixes
    * Many code cleanups
