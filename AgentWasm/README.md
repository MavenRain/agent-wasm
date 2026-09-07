# Binding proof library

Run `lake build` from the repository root using the pinned Lean toolchain.
The library uses Lean core only. Proofs are pure terms, with no tactic blocks.

A downstream Lake project can use a local checkout:

```toml
[[require]]
name = "agent-wasm"
path = "../agent-wasm"
```

Then `import AgentWasm` exposes `AgentWasm.Finite` and its `Phased` namespace.
The latter adds runtime and ghost access rules for finite contexts, with
phase-preserving renaming and substitution results.
See `docs/MECHANIZATION.md` for the exact fragment and remaining obligations.
