# Mechanized finite binding fragment

`AgentWasm/Substitution.lean` begins the binding obligations from
[SEMANTICS.md](SEMANTICS.md). Run `sh scripts/check-proofs.sh` or `lake build`.
`leancho --warn` is an optional local summary tool. A checkout without it
runs `lake build`, whose success line differs. The script also needs `rg`
for its axiom and house-rule audit.
The root Lake package exports `AgentWasm` and pins Lean 4.33.1. It has no
third-party dependencies. Both library and regression targets treat warnings,
including incomplete proof warnings, as errors.

## Exact scope

The model covers non-dependent u32, bool, products, and sums. Its terms are
variables, bounded integer and boolean literals, addition, all three unsigned
comparisons, ordinary conditionals, pairs and projections, sum injections,
case analysis, runtime lets, and annotations. This is a subset of the Execute
fragment. Arithmetic operators have typing rules but no evaluation relation
in this library yet.

`Term n` uses `Fin n` for variable indices. A let body and each case handler
have scope `n + 1`; the let value and case scrutinee remain at `n`. Thus every
representable term is scoped, even when it is ill typed. Literals use
`Fin (2^32)` so out-of-range u32 values cannot enter the model. A numeral
above that bound wraps modulo `2^32`. Lean does not reject it. The OCaml
parser does the range check.

`HasType` is an independent inductive judgment on these scoped terms. A
context maps each valid index to a non-dependent type. `extend` places the
newest type at index zero. All four type constructors are finite, so the
conditional and case result restrictions coincide with this subset of the
source rules. Types contain no term indices and substitution leaves them
unchanged.

## Completed results

| Declaration | Statement |
| --- | --- |
| `rename`, `subst` | Total maps from source scope `n` to target scope `m` |
| `rename_id` | Identity renaming recovers every scoped term |
| `subst_id` | Identity substitution recovers every scoped term |
| `HasType.rename` | A type-preserving variable map preserves typing |
| `HasType.weaken` | Adding a fresh binder and lifting preserves typing |
| `HasType.subst` | Simultaneous typed replacement preserves typing |
| `HasType.instantiate` | Typed binder removal preserves typing |

The simultaneous substitution theorem quantifies over both contexts and
every replacement. It handles open terms, differing context lengths, and
substitution beneath arbitrarily many let or case binders. `liftSub` keeps
the newest variable fixed and weakens each outer replacement. The proofs
cover every constructor explicitly and use pure proof terms. There are no
tactic blocks, project axioms, or incomplete proofs. Lean's axiom inspection
reports only `propext` for the six named theorem results.

`proof-test/BindingTest.lean` checks concrete syntax equations for open
replacement capture, nested lets, shadowing, older indices, case handlers,
all non-binding constructors, and the largest u32 literal. Typed examples
use heterogeneous binders and simultaneous replacements into an empty
context. These examples guard the intended definitions in addition to the
universal theorems. They do not establish implementation correspondence.

## Phase-sensitive finite contexts

`AgentWasm/Phases.lean` reuses the same syntax, binding operations, and
non-dependent typing judgment. `Phased.Quantities` labels each context slot
`run` or `erase`. `Phased.Allowed` checks every variable occurrence:
Execute permits only runtime slots, while Ghost permits either relevance.
Both conditional branches and all eager fields must obey that rule.
The existing let and case forms introduce runtime slots in either phase.

`Phased.HasType` requires both ordinary typing and phase access. Its
`rename`, `weaken`, `subst`, and `instantiate` theorems preserve both
properties. `weaken` adds a run slot and `instantiate` removes a run slot.
Erased binders remain open. Renaming must preserve types and
accessibility. Simultaneous substitution requires every replacement to have
the source slot's type, and requires phase access for replacements of
accessible slots. In Execute, an erased source slot cannot occur in an
allowed term, so its replacement need not be executable. In Ghost, every
replacement must be allowed. `Allowed` holds for every term in Ghost, so
that premise is trivially satisfied.

`Phased.HasType.ghost` lifts any ordinary finite typing derivation into
Ghost. `Phased.erased_var_rejected` rules out an Execute typing derivation
for a variable whose slot is erased. The six audited results report only
`propext` in Lean's transitive axiom inspection.

`proof-test/PhaseTest.lean` covers erased-variable rejection in unselected
branches, eager fields, annotations, comparisons, lets, and both case
handlers. It also checks open replacement under nested binders, ghost
substitution, weakening, inaccessible replacement slots, and rejection of
runtime-to-erased renamings and substitutions. Lake builds this regression
target with warnings as errors alongside the original binding target.

## Remaining boundary

This library does not model Pi, erased let binders, phase transitions within
terms, equality, conversion, records, refinements, Sigma, transport, or
checked branch evidence. Phase access applies to the non-dependent finite
syntax only. It does not prove substitution through dependent context entries.
Renaming composition, substitution composition, and the general
weakening/substitution cancellation law also remain open.

There is no verified translation between this syntax and `lib/ast.ml`, and
the OCaml checker does not consume Lean certificates. The existing named
binding oracle continues to test the production implementation. The parser,
budget accounting, evaluator, erasure, and Wasm backend remain outside this
mechanization. Scope is enforced by the model's indices; this does not show
that the compiler's integer indices or negative shifts preserve scope.

Next extend the binding model to indexed types and erased binders,
then prove dependent typed substitution and establish correspondence with
the implementation. Conversion adequacy, branch realization, preservation,
and erasure simulation remain later obligations. The compiler as a whole
is not formally verified.
