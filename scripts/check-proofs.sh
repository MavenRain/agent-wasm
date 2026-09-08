#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
if command -v leancho >/dev/null 2>&1; then
  leancho --warn
else
  lake build
fi

# Pin the counts for propext-only and axiom-free results separately. The exit
# code of `lake env lean` stays 0 for a project axiom, so audit its report too.
audit_axioms() {
  file=$1
  want=$2
  want_free=${3:-0}
  want_name=${4:-}
  report=$(lake env lean "$file" 2>&1)
  total=$(printf '%s\n' "$report" | rg -c \
    'depends on axioms:|does not depend on any axioms$' || true)
  clean=$(printf '%s\n' "$report" | rg -c 'depends on axioms: \[propext\]$' || true)
  free=$(printf '%s\n' "$report" | rg -c 'does not depend on any axioms$' || true)
  if [ "${total:-0}" != "$want" ] || \
      [ "${clean:-0}" != "$((want - want_free))" ] || \
      [ "${free:-0}" != "$want_free" ]; then
    printf '%s\n' "$report"
    echo "check-proofs: $file needs $want results, $want_free axiom-free." >&2
    echo "check-proofs: found ${total:-0}, ${clean:-0} propext, ${free:-0} free." >&2
    exit 1
  fi
  if [ -n "$want_name" ]; then
    named=$(printf '%s\n' "$report" | rg -c \
      "'.*\.${want_name}' does not depend on any axioms$" || true)
    if [ "${named:-0}" != "$want_free" ]; then
      printf '%s\n' "$report"
      echo "check-proofs: $file must report $want_name as axiom-free." >&2
      exit 1
    fi
  fi
  if [ "$want_free" = 0 ]; then
    echo "OK axioms: $file reports $want results, each [propext]."
  else
    echo "OK axioms: $file reports $want results, $want_free axiom-free, remaining [propext]."
  fi
}

audit_axioms proof-test/BindingTest.lean 6
audit_axioms proof-test/PhaseTest.lean 6
audit_axioms proof-test/BindingLawsTest.lean 14
audit_axioms proof-test/ErasedContextTest.lean 4
audit_axioms proof-test/IndexedTypeTest.lean 23
audit_axioms proof-test/DependentContextTest.lean 7
audit_axioms proof-test/DependentTermTest.lean 13 1 quantityRenaming_access

hits=$(rg -n ':= by|^[[:space:]]*by$|^axiom |^partial |^unsafe |sorry' \
  AgentWasm.lean AgentWasm proof-test || true)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits"
  echo "check-proofs: tactic block, project axiom, or incomplete proof." >&2
  exit 1
fi
echo "OK sources: no tactic block, project axiom, partial, unsafe, or sorry."
