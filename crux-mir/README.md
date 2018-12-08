# haskmir

This is a static simulator for Rust programs.  It includes both a
command line tool (`crux-mir`) and library bindings that can be
integrated with saw-script.

## Preliminaries

You must have the most recent version of the `mir-json` executable in your path.

## Compilation

Use ghc-8.4.3 

    $ cabal new-build

## Execution

    $ cabal new-exec -- crux-mir test/conc_eval/prim/add1.rs

(Should print 2.)

## Command line options

    $ cabal new-exec -- crux-mir --help

## Test suite

    $ cabal new-test

## Test suite with coverage

The `new-*` family of commands is not yet ready for coverage reports. Please run
    $ stack test --coverage
for a coverage report.

## Symbolic execution

Please see the files in `text/symb_eval/` for examples of creating
symbolic values and asserting properties about them.
