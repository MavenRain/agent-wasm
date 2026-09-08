#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
if command -v leancho >/dev/null 2>&1; then
  leancho --warn
else
  lake build
fi

# Every audited result must report propext and nothing else. The exit code of
# `lake env lean` stays 0 for a project axiom, so compare the text and count.
audit_axioms() {
  file=$1
  want=$2
  report=$(lake env lean "$file" 2>&1)
  total=$(printf '%s\n' "$report" | rg -c 'depends on axioms:' || true)
  clean=$(printf '%s\n' "$report" | rg -c 'depends on axioms: \[propext\]$' || true)
  if [ "$total" != "$want" ] || [ "$clean" != "$want" ]; then
    printf '%s\n' "$report"
    echo "check-proofs: $file must report $want results on propext only." >&2
    echo "check-proofs: found $total reports, $clean of them propext only." >&2
    exit 1
  fi
  echo "OK axioms: $file reports $want results, each [propext]."
}

audit_axioms proof-test/BindingTest.lean 6
audit_axioms proof-test/PhaseTest.lean 6
audit_axioms proof-test/BindingLawsTest.lean 14
audit_axioms proof-test/ErasedContextTest.lean 4
audit_axioms proof-test/IndexedTypeTest.lean 23

hits=$(rg -n ':= by|^[[:space:]]*by$|^axiom |^partial |^unsafe |sorry' \
  AgentWasm.lean AgentWasm proof-test || true)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits"
  echo "check-proofs: tactic block, project axiom, or incomplete proof." >&2
  exit 1
fi
echo "OK sources: no tactic block, project axiom, partial, unsafe, or sorry."
