#!/usr/bin/env bash
# Run the Redex type-checker over the crucible-syntax test suite.
#
#   test-data/*.cbl               — must all pass
#   test-data/ux/*.cbl            — must all fail (except SKIP list)
#   crucible-cli test-data/**     — must all pass (except SKIP list)
#
# Exit 0 if the property holds, 1 otherwise.

set -euo pipefail
cd "$(dirname "$0")"

# These ux/ tests exercise Haskell-specific restrictions that
# the Redex model intentionally does not enforce.
UX_SKIP=(
  abs-unsupported
  bad-declare
  binary-wrong-arity
  equal-invalid-type
  equal-needs-annotation
  fresh-non-base
  if-non-base-fp
  numeric-literal-no-annotation
  overloaded-no-annotation
  show-unsupported
)

# These crucible-cli tests are skipped for the following reasons:
#   multi-file       — reference functions/globals defined in other files
#                      (assumption-state, debug, override-*, conc-bool, mjrty)
#   bare nothing/seq-nil — need explicit type annotations, e.g. (the (Maybe T) nothing)
#                      (from-maybe, seq-test*)
CLI_SKIP=(
  assumption-state
  conc-bool
  debug
  from-maybe
  mjrty
  override-nondet-test-0
  override-nondet-test-1
  override-nondet-test-both
  override-nondet-test-neither
  override-test
  override-test2
  seq-test1
  seq-test2
  seq-test3
)

ok=true

in_list() {
  local needle=$1; shift
  for s in "$@"; do
    if [ "$needle" = "$s" ]; then return 0; fi
  done
  return 1
}

# --- Positive tests (should all pass) ---
for f in ../test-data/*.cbl; do
  if ! racket check.rkt "$f"; then
    ok=false
  fi
done

# --- Negative tests (should all fail) ---
for f in ../test-data/ux/*.cbl; do
  base=$(basename "$f" .cbl)
  if in_list "$base" "${UX_SKIP[@]}"; then continue; fi

  if racket check.rkt "$f" 2>/dev/null | grep -q "OK"; then
    echo "SHOULD FAIL but passed: $f"
    ok=false
  fi
done

# --- crucible-cli tests (should all pass) ---
for f in ../../crucible-cli/test-data/**/*.cbl; do
  base=$(basename "$f" .cbl)
  if in_list "$base" "${CLI_SKIP[@]}"; then continue; fi

  if ! racket check.rkt "$f"; then
    ok=false
  fi
done

$ok
