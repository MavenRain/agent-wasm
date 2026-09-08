# Roadmap

## M0: checked erasure to executable Wasm

Implemented: explicit dependent core, quantity-zero arguments, equality evidence,
shared checking budget, proof-free runtime IR, direct integer Wasm emission,
CLI, rejection tests, differential host execution, and an informational OCaml
comparison harness. The name and surface syntax remain provisional.

Hardening: decimal-only literal syntax, a 50,000 combined parameter/local backend
limit, a separate 1,000 entry-parameter limit, consistent binder-name validation,
and host regressions for boundary rejection and parameter order are in place.
Backend expansion threads immutable state explicitly through eager evaluation.

## M1: dependent data and executable validation

Implemented first slice: internal booleans, unsigned u32 comparisons, and u32
conditionals with executable Wasm branches. The price-ceiling example returns
an integer decision. The existing integer export ABI remains unchanged. Closed
comparisons and conditionals participate in definitional conversion. Directed
and generated programs are checked against an independent interpreter on both hosts.

Next: extend the restricted dependent syntax and its index language, then
prove general dependent typed substitution through context suffixes and
connect the model to the implementation. Include computed dependent
projections and the remaining source constructs. Then cover conversion
adequacy, branch realization, and erasure simulation.
Named error variants and a reusable surface for these contracts remain open.

Implemented second slice: non-dependent products, eager pairs, and projections,
including nested products and internal function fields. Static expansion retains
both fields' runtime computations without introducing an object ABI. The
tool-policy example packages a proposed action and checks immutable tool IDs
and a price ceiling, returning an integer decision.

Implemented third slice: boolean-valued conditionals compose scalar predicates.
The budget-policy example detects u32 addition overflow before checking a ceiling,
so wrapping cannot turn an excessive proposal into an accepted one. It returns
an integer decision.

Implemented fourth slice: explicit equality transport over u32-indexed type
families. Endpoints and equality evidence are checked in the ghost phase; the
transported value is checked in the enclosing phase. Erasure keeps only the
value because type indices cannot change runtime representation in this
fragment. Abstract symmetry and transitivity are expressible. Reflexive
transport reduces during conversion; transport with an open proof stays
symbolic. The symmetry example emits the same module as plain increment.
Transport itself consumes existing equality evidence.

Implemented fifth slice: conditionals return nested products of scalar fields.
The budget-result example returns an internal status/payload pair, distinguishing
overflow from exceeding a ceiling and retaining the accepted total. Selected
branch computations execute once, followed by scalar field selection.

Implemented sixth slice: internal sums with explicit injections and case
handlers. Payloads and case results support nested scalar products and sums.
The budget-sum example distinguishes error codes from successful totals using
the type system, then adapts its result to the integer ABI. Lowering reuses
products and executable conditionals with a tag and inactive payload storage.

Implemented seventh slice: refined values pair a finite runtime payload with
an erased dependent equality proof. Explicit pack, value, and evidence forms
check construction and projection without introducing runtime wrappers.
Refinements compose inside products, sums, conditionals, and case results;
all indexed families are checked before erasure. The refined-increment example
carries evidence of its modular result and emits the same IR and Wasm as the
equivalent plain program. An ordinary conditional does not refine its branches.

Implemented eighth slice: `if-proof` binds erased evidence in each executable
branch. The evidence states that the condition's u32 indicator equals 1 or 0,
using the existing equality type. An explicit finite result type prevents the
branch binder from escaping. The validated-ceiling example returns an internal
error/refined-value sum and adapts it to the integer ABI. Its successful payload
carries evidence that it meets the supplied ceiling. Arithmetic still wraps.

Implemented ninth slice: internal named records with eager field construction
and checked projection. Ordered, structural record types contain finite payloads
and compose with refinements, sums, and checked branches. Field names do not
bind indices or survive in Wasm. The record-policy example checks an immutable
tool allowlist and price ceiling, returning an error or a refined named action
before adapting to the scalar ABI.

Implemented tenth slice: finite dependent pairs with `(sigma (x A) B)` and
annotated `dpair` construction. Both components survive as an ordinary runtime
pair; the second component's type may refer to the first through erased
evidence indices. Dependent projection, substitution, conversion, and formation
compose with the existing finite data forms. Function-bearing pairs with
dependent types, explicitly erased Sigma components, and type-level shape
selection remain outside this slice.

The validated-budget example combines false-branch overflow evidence with
true-branch ceiling evidence in nested refinements. Its successful dependent
pair retains the starting balance and accepted total; its error sum
distinguishes overflow from exceeding the ceiling. The integer adapter exposes
status or payload. Arithmetic remains modular, with explicit overflow rejection.

Implemented eleventh slice: explicit evaluation and typing rules, an erasure
relation, and qualified proof obligations in `docs/SEMANTICS.md`. Independent
named-syntax binding tests exercise capture-avoiding substitution under nested
term and type binders. The validated-tool-budget example composes the immutable
allowlist with overflow and ceiling checks, retaining distinct errors and
checked evidence for the accepted action and its computed total.

Implemented twelfth slice: a reusable Lean library for scoped non-dependent
finite syntax, identity binding laws, weakening, simultaneous typed
substitution, and binder removal. It covers scalar, product, and sum types
with lets and case handlers. The proofs do not cover dependent types or
establish correspondence with the OCaml implementation. See
`docs/MECHANIZATION.md` for the exact claims and remaining boundary.

Implemented thirteenth slice: phase-sensitive contexts over the same finite
syntax, with runtime and erased variable slots. Renaming, weakening,
simultaneous typed substitution, and runtime binder removal preserve access
in Execute or Ghost. Regressions reject erased-variable access beneath
binders and in unselected branches.

Implemented fourteenth slice: indexed equality, refinement, product, sum,
and Sigma type schemas over finite contexts and finite binder domains.
Renaming and typed finite substitution preserve their formation; open
replacements lift beneath both refinement and Sigma binders. Term and schema
binding laws cover composition, weakening cancellation, and commuting
substitution with instantiation. Schema representation and branch eligibility
are invariant under index substitution. Erased context slots support weakening
and removal using Ghost replacements while preserving the enclosing phase.
These results do not type dependent terms or dependent context entries.

Implemented fifteenth slice: scoped dependent telescopes with lookup shifting,
formation of their declarations, and conservative finite index typing.
Dependent equality, refinement, and Sigma entries retain their source schemas;
no runtime shape coercion makes them finite indices. Renaming and weakening
preserve index typing and schema formation, and lookup in a formed telescope
returns a formed schema.

A restricted dependent value language adds Ghost equality evidence, refined
packages with Ghost proofs, payload projection, finite-domain dependent pairs
and first projection, products, sum injections, conditionals, annotations,
and lets of either relevance. Let results are weakened outer schemas, so
the new binder cannot escape. Result formation, runtime eligibility, renaming,
weakening, and identity renaming are proved. Execute rejects equality results
and erased variables. This slice does not add general dependent substitution,
computed dependent projection indices, evidence projection, Sigma second
projection, conversion, transport, or checked branch evidence to the model.

Dependent substitution, preservation, and erasure simulation remain unproved
for the general supported fragment. Establish them before calling it
verified. Keep adversarial examples and an independent reference semantics
alongside mechanization.

## M2: host boundary and ML surface

Add an ergonomic surface over the checked core, stable module interfaces, typed
errors, and explicit effects. Introduce host imports through declared capabilities,
with typed HTTP/JSON bindings and a mock inference provider first. Version schemas
and preserve runtime validation of remote responses.

Choose the WasmGC object representation and the host resource ABI together. Keep
Wasm imports small and explicit. Add real closures and direct function calls so
the development compiler does not depend on whole-program static expansion.

## M3: controlled agent execution

Add affine resources, structured concurrency, cancellation, protocol states,
secret labels, and controlled disclosure. Cover logging and implicit information
flows. Wire typed inference and MCP clients through explicit host authority.
The first acceptance application is a private proxy with a constrained tool agent.

## M4: durable resources and representative speed gates

Add reservation and reconciliation libraries, durable workflow state, idempotency,
and explicit remote protocol assumptions. Validate budgets, revocation, freshness,
and payment state at runtime. Add a streaming media pipeline as another corpus.

Make OCaml-speed compilation a measured gate over representative applications:
clean builds including fresh proof checking, implementation edits, proof-only
edits, and contract edits. Pin compiler versions, machine, parallelism, output
targets, cache state, and full samples. Opaque module interfaces, bounded proof
automation, and checked artifact reuse are intended mechanisms, not established
performance claims. Runtime throughput and output size must also be recorded.

Application work does not wait until M4 to measure performance. The M0 harness
runs now, and each milestone expands its corpus and reports regressions. M4's
gate replaces the toy comparison with the workloads named above.
