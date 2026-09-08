# Binding proof library

Run `lake build` from the repository root using the pinned Lean toolchain.
The library uses Lean core only. Proofs are pure terms, with no tactic blocks.

A downstream Lake project can use a local checkout:

```toml
[[require]]
name = "agent-wasm"
path = "../agent-wasm"
```

Then `import AgentWasm` exposes `AgentWasm.Finite`, its `Phased` namespace,
and `AgentWasm.Indexed`. Finite terms have binding composition laws and
phase-preserving substitution, including removal of erased context binders.
Indexed type schemas have formation-preserving substitution over finite
contexts, binding composition, and invariance of a schema shape function
under index maps. Their domains remain non-dependent finite types;
dependent term typing remains open.
See `docs/MECHANIZATION.md` for the exact fragment and remaining obligations.
