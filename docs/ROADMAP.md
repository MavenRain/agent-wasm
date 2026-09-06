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

Next: add sums, records, dependent pairs, and equality transport
with a precise erasure rule. Represent validation as an executable branch yielding
either an error or a value with erased evidence. First domain example: a proposed
tool action checked against an explicit immutable allowlist and price ceiling.
Amounts need non-wrapping arithmetic or explicit overflow errors.

Implemented second slice: non-dependent products, eager pairs, and projections,
including nested products and internal function fields. Static expansion retains
both fields' runtime computations without introducing an object ABI. The
tool-policy example packages a proposed action and checks immutable tool IDs
and a price ceiling, returning an integer decision. Evidence-bearing validation
and named records remain open.

Implemented third slice: boolean-valued conditionals compose scalar predicates.
The budget-policy example detects u32 addition overflow before checking a ceiling,
so wrapping cannot turn an excessive proposal into an accepted one. It returns
an integer decision; distinct overflow errors and evidence-bearing results remain
open.

Write small-step or evaluation semantics, typing rules, and an erasure relation.
Establish substitution, preservation, and erasure simulation for the supported
fragment before calling it verified. Use adversarial examples and an independent
reference semantics alongside mechanization.

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
