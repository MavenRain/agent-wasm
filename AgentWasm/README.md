# Binding and dependent typing proof library

Run `lake build` from the repository root using the pinned Lean toolchain.
The library uses Lean core only. Proofs are pure terms, with no tactic blocks.

A downstream Lake project can use a local checkout:

```toml
[[require]]
name = "agent-wasm"
path = "../agent-wasm"
```

Then `import AgentWasm` exposes `AgentWasm.Finite`, its `Phased` namespace,
`AgentWasm.Indexed`, and `AgentWasm.Dependent`. Finite terms have binding laws
and phase-preserving substitution, including removal of erased context binders.
Indexed type schemas have formation-preserving substitution over finite
contexts, binding composition, and invariance of a schema shape function
under index maps. Their domains remain non-dependent finite types.

Dependent telescopes store scoped schemas over preceding entries. Their finite
index typing accepts only explicit base declarations, with no coercion from a
dependent type to its runtime shape. Restricted dependent terms include Ghost
equality evidence, refinement construction and payload projection, finite-domain
dependent pairs and first projection, products, sum injections, conditionals,
annotations, and lets with either relevance. Renaming and weakening preserve
their phase-sensitive typing, and every typed result has a formed schema.
General dependent substitution and compiler correspondence remain open.
See `docs/MECHANIZATION.md` for the exact fragment and remaining obligations.
