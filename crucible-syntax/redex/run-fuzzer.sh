#!/usr/bin/env bash
set -euo pipefail

# Default configuration
COUNT=5000
SIZE=15
TYPE_STATS=1
CHECK_PARSER=1
OUTPUT_DIR=""

# Usage information
usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Run the Crucible syntax fuzzer with type-checking and parser validation.

OPTIONS:
    -c, --count NUM       Number of programs to generate (default: 5000)
    -s, --size NUM        Maximum program size (default: 15)
    -o, --output DIR      Output directory for generated programs
    --no-parser-check     Skip parser validation (only type-check)
    --no-type-check       Skip type-checking (generate all programs)
    -h, --help            Show this help message

EXAMPLES:
    # Run with defaults (5000 programs, size 15)
    $0

    # Quick test (100 small programs)
    $0 -c 100 -s 5

    # Generate programs to specific directory
    $0 -c 1000 -s 10 -o ./generated-programs

    # Only generate and type-check (no parser validation)
    $0 --no-parser-check

EOF
    exit 0
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -c|--count)
            COUNT="$2"
            shift 2
            ;;
        -s|--size)
            SIZE="$2"
            shift 2
            ;;
        -o|--output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --no-parser-check)
            CHECK_PARSER=0
            shift
            ;;
        --no-type-check)
            TYPE_STATS=0
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            echo "Error: Unknown option $1"
            usage
            ;;
    esac
done

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Build command
FUZZ_CMD="racket fuzz.rkt --count $COUNT --size $SIZE"

if [[ $TYPE_STATS -eq 1 ]]; then
    FUZZ_CMD="$FUZZ_CMD --type-stats"
fi

if [[ $CHECK_PARSER -eq 1 ]]; then
    FUZZ_CMD="$FUZZ_CMD --crucible yes"
fi

if [[ -n "$OUTPUT_DIR" ]]; then
    mkdir -p "$OUTPUT_DIR"
    FUZZ_CMD="$FUZZ_CMD --write $OUTPUT_DIR"
fi

echo "========================================"
echo "Crucible Syntax Fuzzer"
echo "========================================"
echo "Configuration:"
echo "  Programs:     $COUNT"
echo "  Max size:     $SIZE"
echo "  Type-check:   $([[ $TYPE_STATS -eq 1 ]] && echo "yes" || echo "no")"
echo "  Parser check: $([[ $CHECK_PARSER -eq 1 ]] && echo "yes" || echo "no")"
[[ -n "$OUTPUT_DIR" ]] && echo "  Output dir:   $OUTPUT_DIR"
echo "========================================"
echo

# Run the fuzzer
eval "$FUZZ_CMD"

exit_code=$?

if [[ $exit_code -eq 0 ]]; then
    echo
    echo "✅ Fuzzer completed successfully!"
else
    echo
    echo "❌ Fuzzer failed with exit code $exit_code"
fi

exit $exit_code
