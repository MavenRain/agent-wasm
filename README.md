# agent-wasm

An OCaml implementation of a small dependently typed language that checks proofs,
erases them before runtime lowering, and emits WebAssembly directly. `agent-wasm`
is a working name. The intended applications are private inference clients,
constrained agents, and durable tool and payment workflows.

The first executable milestone is a pure compiler foundation. It supports u32
arithmetic, booleans, unsigned comparisons, conditional branches, pairs, dependent
function types, erased arguments, equality evidence, and equality transport.
It does not yet implement agent APIs, effects, ownership, evidence-bearing validators,
cryptography, or persistence. Proof checking and erasure are tested, not formally
proved. OCaml-speed compilation remains a project acceptance requirement.

## Run

Requirements: OCaml 5.2 or newer, Dune 3.17 or newer, Node with WebAssembly support.
The compiler has no third-party OCaml dependencies. Full validation also uses
Wasmtime. `dunecho` is an optional installed build-output wrapper.

```sh
opam exec -- dune build
mkdir -p artifacts
_build/default/bin/main.exe compile examples/dependent.aw artifacts/dependent.wasm
node scripts/run.mjs artifacts/dependent.wasm 41
# 42
_build/default/bin/main.exe ir examples/increment.aw
# (export main (fn (add v0 1)))
```

The output is a standalone core Wasm module exporting `main`. It has no imports,
memory, WASI dependency, or ambient host capabilities. A Wasmtime invocation is:

```sh
wasmtime run -C cache=n --invoke main artifacts/dependent.wasm 41
```

Wasm i32 uses the same bits as source u32. Node's runner renders unsigned results;
Wasmtime's CLI expects and prints signed i32 values, so use `-1` for 4294967295.

## A checked program

```lisp
(export main
  (fn (run x u32)
    (let (erase same (eq x x)) (refl x)
      (add x 1))))
```

`eq` is indexed by expressions, not just types. `refl x` establishes `eq x x`.
The compiler also checks beta conversion and closed modular arithmetic. The
proof, its type, and its binder disappear before Wasm lowering. This example
produces exactly the same runtime IR and Wasm bytes as the proof-free version.
`examples/dependent.aw` additionally demonstrates a function whose proof argument
type depends on two previous value arguments.

```sh
_build/default/bin/main.exe check examples/reject-false-proof.aw
# exits 1: type mismatch
_build/default/bin/main.exe check examples/reject-erased-use.aw
# exits 1: erased variable used at runtime
```

The provisional syntax is an explicit S-expression core. A friendly ML surface
will be added over the same checker. All applications explicitly select `run` or
`erase`; there is no implicit proof search or axiom escape hatch.

The first M1 slice adds an executable price predicate:

```sh
_build/default/bin/main.exe compile examples/price-ceiling.aw artifacts/price-ceiling.wasm
node scripts/run.mjs artifacts/price-ceiling.wasm 100
# 1
node scripts/run.mjs artifacts/price-ceiling.wasm 101
# 0
```

Comparisons produce internal booleans and `if` selects matching u32, bool, or nested product
branches. Sums and validators returning values with erased evidence remain
on the M1 roadmap.

This slice adds `(product A B)`, `(pair a b)`, `fst`, and `snd` for internal
data. `examples/tool-policy.aw` packages a tool ID and price, then checks IDs 7
and 9 against a price ceiling of 100:

```sh
_build/default/bin/main.exe compile examples/tool-policy.aw artifacts/tool-policy.wasm
node scripts/run.mjs artifacts/tool-policy.wasm 7 100
# 1
node scripts/run.mjs artifacts/tool-policy.wasm 8 100
# 0
```

Both pair fields evaluate eagerly. The public ABI still accepts and returns
integers; this example returns a decision without granting host authority.

Boolean branches let predicates compose. `examples/budget-policy.aw` accepts
spent, proposed, and ceiling, returning 1 only when their non-wrapping sum fits:

```sh
_build/default/bin/main.exe compile examples/budget-policy.aw artifacts/budget-policy.wasm
node scripts/run.mjs artifacts/budget-policy.wasm 60 40 100
# 1
node scripts/run.mjs artifacts/budget-policy.wasm 4294967295 1 100
# 0
```

The example detects overflow before comparing the modular total with the ceiling.

`examples/budget-result.aw` returns an internal `(product u32 u32)` from a
conditional: status 0 with the accepted total, status 1 with zero for overflow,
or status 2 with zero for exceeding the ceiling. Its fourth integer argument
selects the status (0) or payload (any other value), preserving the integer ABI.

```sh
_build/default/bin/main.exe compile examples/budget-result.aw artifacts/budget-result.wasm
node scripts/run.mjs artifacts/budget-result.wasm 60 40 100 1
# 100
node scripts/run.mjs artifacts/budget-result.wasm 4294967295 1 100 0
# 1
node scripts/run.mjs artifacts/budget-result.wasm 60 41 100 0
# 2
```
It returns a decision; structured errors and evidence-bearing results remain open.

Equality transport rewrites a type family using checked evidence:
`(transport (index FAMILY) from to proof value)` takes a value of `FAMILY[from]`
to `FAMILY[to]`, requiring `proof : (eq from to)`. The family binds a ghost u32
index. For example, `(transport (x (eq x a)) a b proof (refl a))` derives
`eq b a` from `proof : eq a b` in a ghost context.

`examples/transport.aw` defines this symmetry helper and uses it in an increment
program. It emits the same runtime IR and Wasm bytes as `increment-plain.aw`.
Transport preserves only its value at runtime; it cannot replace executable
validation or turn a comparison into a proof.

## Validate

```sh
sh scripts/check.sh
opam exec -- python3 -P scripts/bench.py
```

Without `dunecho`, use `opam exec -- dune build`, then run
`_build/default/test/kernel_test.exe` and `node scripts/e2e.mjs` directly.
The e2e suite compares generated programs against an independent named-variable
evaluator in both Node and Wasmtime. It checks binary equality after erasure,
u32 boundaries, multi-byte encodings, variable capture, malformed inputs, and
rejection without output mutation.

The benchmark compares fresh compiler invocations with `ocamlopt -c` on matched
u32 arithmetic workloads, including proof-bearing and transport versions. It records all
samples, input hashes, compiler hash, and environment under `artifacts/bench/`.
Wasm module emission and native object emission are different tasks. This small
benchmark cannot establish application-scale or incremental compilation parity.

See [the specification](docs/SPEC.md), [the roadmap](docs/ROADMAP.md), and
[validation evidence](docs/VALIDATION.md).
