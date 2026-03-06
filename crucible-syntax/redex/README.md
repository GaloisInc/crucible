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
# Quick test (100 attempts, size 3)
racket fuzz.rkt -n 100 -s 3

# Full fuzzer run with type-checking (1000 attempts, generate 5000 programs, size 15)
racket fuzz.rkt -n 1000 -s 15 --count 5000 --type-stats

# Save generated programs to directory
racket fuzz.rkt -n 500 -s 10 --count 1000 --type-stats --write ./output-dir

# With Haskell parser validation (if crucible-syntax binary is available)
racket fuzz.rkt -n 500 -s 10 --count 1000 --type-stats --crucible path/to/crucible-syntax
```

Options:
- `-n, --attempts N` - Number of round-trip tests (default: 1000)
- `-s, --size N` - Maximum term size (default: 5)
- `--count N` - Number of programs to generate (default: 100)
- `--type-stats` - Generate and type-check programs
- `--write DIR` - Save generated .cbl files to directory
- `--crucible PATH` - Test Haskell parser on well-typed programs using crucible-syntax executable

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
