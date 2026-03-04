# Crucible-Syntax Redex specification

A formal specification and reference implementation of the Crucible intermediate language syntax using PLT Redex.

## Overview

This directory contains:
- **Grammar definition** (`grammar.rkt`) - Formal grammar for Crucible syntax
- **Type system** (`typing.rkt`) - Type-checking rules and judgments
- **Parser** (`parse.rkt`) - S-expression parser that transforms surface syntax to AST
- **Type checker** (`check.rkt`) - Command-line tool for validating `.cbl` files
- **Fuzzer** (`fuzz.rkt`) - Property-based testing via random program generation
- **Documentation** (`doc.rkt`, `doc/`) - Auto-generated reference documentation

## Usage

### Requirements

- [Racket](https://racket-lang.org/) 8.0+
- Redex package (included with Racket distribution)

### Type-check a program

```bash
racket check.rkt path/to/program.cbl
```

### Run the test suite

```bash
./test-suite.sh
```

### Run the fuzzer

```bash
# Quick test
./run-fuzzer.sh -c 100 -s 5

# Full fuzzer run (5000 programs, size 15)
./run-fuzzer.sh

# Save generated programs
./run-fuzzer.sh -c 1000 -s 10 -o ./output-dir

# Options
./run-fuzzer.sh --help
```

### Generate documentation

```bash
racket doc.rkt
# Opens documentation in browser
```

## Testing

The specification is tested via:

1. **Unit tests** - Hand-written `.cbl` programs in `../test-data/`
2. **Fuzzer** - Generates random programs and validates:
   - Parser round-trip: `parse(unparse(ast)) = ast`
   - Well-typed programs parse correctly
   - Type-checker finds issues in ill-typed programs
