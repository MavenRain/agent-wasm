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
# The fifth argument pins the reported declaration names. A count alone accepts
# a duplicated or swapped `#print axioms` line; the name list rejects it.
audit_axioms() {
  file=$1
  want=$2
  want_free=${3:-0}
  want_name=${4:-}
  want_names=${5:-}
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
  for one in $want_names; do
    seen=$(printf '%s\n' "$report" | rg -c \
      "'.*\.${one}' (depends on axioms:|does not depend on any axioms\$)" || true)
    if [ "${seen:-0}" != 1 ]; then
      printf '%s\n' "$report"
      echo "check-proofs: $file must report $one exactly once." >&2
      exit 1
    fi
  done
  if [ "$want_free" = 0 ]; then
    echo "OK axioms: $file reports $want results, each [propext]."
  else
    echo "OK axioms: $file reports $want results, $want_free axiom-free, remaining [propext]."
  fi
}

binding_names='HasType.rename HasType.weaken HasType.subst HasType.instantiate
  rename_id subst_id'
phase_names='HasType.rename HasType.weaken HasType.subst HasType.instantiate
  HasType.ghost erased_var_rejected'
laws_names='rename_composition rename_comp rename_congr rename_weaken
  subst_renaming subst_rename subst_congr rename_substitution rename_subst
  subst_weaken subst_composition subst_comp instantiate_weaken
  subst_instantiate'
erased_names='Allowed.weakenWith HasType.weakenWith
  Allowed.instantiate_erased HasType.instantiate_erased'
indexed_names='rename_id subst_id branch_rename branch_subst WellFormed.rename
  WellFormed.weaken WellFormed.subst WellFormed.instantiate
  WellFormed.subst_ghost shape_rename shape_subst rename_comp subst_rename
  rename_subst subst_comp instantiate_weaken subst_instantiate rename_identity
  subst_identity rename_composition subst_renaming rename_substitution
  subst_composition'
depcontext_names='rename_weaken liftRen_preserves IndexHasType.rename
  IndexHasType.weaken WellFormed.rename WellFormed.weaken
  Context.WellFormed.lookup'
depterm_names='rename_identity rename_id runtimeType_rename HasType.wellFormed
  HasType.runtimeType execute_equality_rejected erased_var_rejected
  index_rename_instantiate schema_rename_instantiate quantityRenaming_access
  quantityRenaming_lift HasType.rename HasType.weaken'
depbranch_names='indicator_rename branchEvidence_rename indicator_hasType
  branchEvidence_wellFormed'
depindex_names='IndexHasSchema.rename IndexHasSchema.weaken
  IndexHasSchema.branchType IndexHasSchema.wellFormed'

audit_axioms proof-test/BindingTest.lean 6 0 '' "$binding_names"
audit_axioms proof-test/PhaseTest.lean 6 0 '' "$phase_names"
audit_axioms proof-test/BindingLawsTest.lean 14 0 '' "$laws_names"
audit_axioms proof-test/ErasedContextTest.lean 4 0 '' "$erased_names"
audit_axioms proof-test/IndexedTypeTest.lean 23 0 '' "$indexed_names"
audit_axioms proof-test/DependentContextTest.lean 7 0 '' "$depcontext_names"
audit_axioms proof-test/DependentTermTest.lean 13 1 quantityRenaming_access \
  "$depterm_names"
audit_axioms proof-test/DependentBranchTest.lean 4 0 '' "$depbranch_names"
audit_axioms proof-test/DependentIndexTest.lean 4 0 '' "$depindex_names"

hits=$(rg -n ':= by|^[[:space:]]*by$|^axiom |^partial |^unsafe |sorry' \
  AgentWasm.lean AgentWasm proof-test || true)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits"
  echo "check-proofs: tactic block, project axiom, or incomplete proof." >&2
  exit 1
fi
echo "OK sources: no tactic block, project axiom, partial, unsafe, or sorry."
