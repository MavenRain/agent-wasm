# Mechanized binding and indexed type formation

`AgentWasm/Substitution.lean` begins the binding obligations from
[SEMANTICS.md](SEMANTICS.md). Run `sh scripts/check-proofs.sh` or `lake build`.
`leancho --warn` is an optional local summary tool. A checkout without it
runs `lake build`, whose success line differs. The script also needs `rg`
for its axiom and house-rule audit.
The root Lake package exports `AgentWasm` and pins Lean 4.33.1. It has no
third-party dependencies. Both library and regression targets treat warnings,
including incomplete proof warnings, as errors.

## Finite term scope

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

## Finite term results

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

`AgentWasm/BindingLaws.lean` adds renaming composition, substitution after
renaming, renaming after substitution, and substitution composition. Each
law has a pointwise form and an ordinary composition corollary. Open
replacements are renamed when crossing binders. Further results show that
instantiating a weakened term cancels the unused binder, and that
substitution commutes with instantiation when lifted in the body.

`proof-test/BindingLawsTest.lean` pins the explicit result of two open
substitutions through both case branches and nested lets. It also applies
the general laws to used and unused binders. Its 14 audited declarations
report only `propext`.

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
Renaming must preserve types and accessibility. Simultaneous substitution
requires every replacement to have
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

`AgentWasm/ErasedContexts.lean` adds `extendWith` and `weakenWith` for either
context slot relevance. `HasType.instantiate_erased` removes an erased
context slot using a Ghost-typed replacement while preserving the body's
original phase. In Execute the body cannot use that slot; in Ghost it can.
This concerns external contexts. The finite term syntax still has only
runtime lets and runtime case payload binders. It does not model an erased
let term or a transition from Execute to Ghost inside a term.
`proof-test/ErasedContextTest.lean` checks both relevance weakenings, open
Ghost replacements, nested lets and cases, and forbidden Execute access.
All four audited results report only `propext`.

## Indexed type schemas

`AgentWasm/IndexedTypes.lean` introduces `Indexed.Ty n` with six forms:
finite base types, equality, products, sums, refinements, and Sigma pairs.
Equality endpoints are scoped finite terms. A refinement binds its finite
payload in two equality endpoints, and a Sigma binds its finite domain in
the result schema. Both binders increase the endpoint scope by one.
Products and sums can contain indexed schemas recursively.

The domains of refinements and Sigma pairs are deliberately restricted to
`Finite.Ty`. Context entries also stay finite and non-dependent. In
particular, the model does not substitute a refined variable's payload
shape for its source type: the source checker requires an explicit `value`
projection. Terms cannot carry indexed type annotations or produce refined
or dependent-pair values in this model.

`WellFormed` checks both equality endpoints at u32 using the existing finite
typing judgment. This is equivalent to Ghost typing for any relevance map
by `Phased.HasType.ghost`. Type indices may read erased variables. A
refinement checks endpoints under its payload binder. A Sigma checks its
range under its domain binder. Sums and Sigma ranges require `BranchType`,
which rejects equality outside refinement evidence. Products may contain
ghost equality schemas, as in source type formation, but those products
are not branch types. These rules describe the corresponding restricted
cases of `lib/kernel.ml`; that correspondence has not been proved.

| Declaration in `AgentWasm.Indexed` | Statement |
| --- | --- |
| `rename_id`, `subst_id` | Identity maps preserve every scoped schema |
| `WellFormed.rename`, `weaken` | Typed variable maps preserve formation |
| `WellFormed.subst`, `instantiate` | Typed replacement preserves formation |
| `WellFormed.subst_ghost` | A Ghost typed replacement preserves formation |
| `rename_comp`, `subst_rename` | Renaming composes with either binding map |
| `rename_subst`, `subst_comp` | Open replacements compose under both binders |
| `instantiate_weaken` | Removing an unused binder cancels weakening |
| `subst_instantiate` | Outer substitution commutes with family instantiation |
| `branch_rename`, `branch_subst` | Binding maps preserve branch eligibility |
| `shape_rename`, `shape_subst` | Indices cannot change representation |

For example, instantiating `eq (var 0) (var 0)` with `uint 7` changes both
endpoints. Instantiating `refine u32 (var 0) (var 1)` preserves its bound
payload at index zero and replaces only the outer variable. Nested Sigma
and refinement binders lift open replacements twice. The composition and
instantiation laws quantify over arbitrary scoped schemas, including
ill-formed schemas; formation preservation separately requires typed
replacements and a well-formed input.

`shape` returns a finite representation or `none` for exposed equality.
Refinements keep their payload shape and Sigma pairs use product shapes.
Its invariance theorems are about this function on schemas. They do not
establish erasure simulation or validate the compiler's representation.

`proof-test/IndexedTypeTest.lean` pins explicit results under nested type
binders, uses heterogeneous contexts and open Ghost replacements, rejects
boolean equality endpoints and proof-bearing sum or Sigma ranges, and
checks the binding laws. Its 23 audited results report only `propext`.
All five regression targets are default Lake targets with warnings as
errors, and `scripts/check-proofs.sh` checks every expected axiom report.

## Remaining boundary

This library does not model dependent term typing, Pi, erased let terms,
phase transitions within terms, conversion, records, transport, or checked
branch evidence. Equality, refinement, and Sigma occur only as indexed type
schemas with finite binder domains. There is no typing relation for their
proofs, packages, or dependent pairs. Phase access applies to finite terms;
dependent context entries and substitution through them remain open.

There is no verified translation between this syntax and `lib/ast.ml`, and
the OCaml checker does not consume Lean certificates. The existing named
binding oracle continues to test the production implementation. The parser,
budget accounting, evaluator, erasure, and Wasm backend remain outside this
mechanization. Scope is enforced by the model's indices; this does not show
that the compiler's integer indices or negative shifts preserve scope.

Next extend indexed formation to dependent contexts and binder domains,
add dependent term typing and erased term binders, then prove dependent
typed substitution and establish correspondence with the implementation.
Conversion adequacy, branch realization, preservation, and erasure simulation
remain later obligations. The compiler as a whole is not formally verified.
