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

# These crucible-cli tests are skipped because they reference overrides that are
# not modeled in the Redex spec.
CLI_SKIP=(
  assumption-state
  conc-bool
  debug
  mjrty
  override-nondet-test-0
  override-nondet-test-1
  override-nondet-test-both
  override-nondet-test-neither
  override-test
  override-test2
)

ok=true
pos_pass=0
pos_fail=0
neg_pass=0
neg_fail=0
cli_pass=0
cli_fail=0
cli_skip=0

in_list() {
  local needle=$1; shift
  for s in "$@"; do
    if [ "$needle" = "$s" ]; then return 0; fi
  done
  return 1
}

echo "=== Positive tests (test-data/*.cbl) ==="
for f in ../test-data/*.cbl; do
  if racket check.rkt "$f"; then
    pos_pass=$((pos_pass + 1))
  else
    ok=false
    pos_fail=$((pos_fail + 1))
  fi
done

echo ""
echo "=== Negative tests (test-data/ux/*.cbl) ==="
for f in ../test-data/ux/*.cbl; do
  base=$(basename "$f" .cbl)
  if in_list "$base" "${UX_SKIP[@]}"; then continue; fi

  if racket check.rkt "$f" 2>/dev/null | grep -q "OK"; then
    echo "SHOULD FAIL but passed: $f"
    ok=false
    neg_fail=$((neg_fail + 1))
  else
    neg_pass=$((neg_pass + 1))
  fi
done

echo ""
echo "=== crucible-cli tests ==="
for f in ../../crucible-cli/test-data/**/*.cbl; do
  base=$(basename "$f" .cbl)
  if in_list "$base" "${CLI_SKIP[@]}"; then
    cli_skip=$((cli_skip + 1))
    continue
  fi

  if racket check.rkt "$f"; then
    cli_pass=$((cli_pass + 1))
  else
    ok=false
    cli_fail=$((cli_fail + 1))
  fi
done

echo ""
echo "=== Summary ==="
echo "Positive tests:  $pos_pass passed, $pos_fail failed"
echo "Negative tests:  $neg_pass passed (correctly failed), $neg_fail failed (incorrectly passed)"
echo "CLI tests:       $cli_pass passed, $cli_fail failed, $cli_skip skipped"
echo ""

if $ok; then
  echo "✓ All tests passed"
  exit 0
else
  echo "✗ Some tests failed"
  exit 1
fi
