# M0 validation, 2026-09-06

Environment: macOS arm64, OCaml 5.2.1, Dune 3.24.2, Node v23.10.0,
Wasmtime 48.0.1. Commands run from the project root.

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 31 cases, 0 failures
  e2e: 107 programs, 214 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny lib bin test
  no obligations at or above medium in 14 files
```

The 31 kernel cases cover dependent argument substitution and mismatch,
capture avoidance, relevance errors, equality formation, closed and beta
conversion, u32 modular behavior, erased binder remapping, higher-order internal
functions, export restrictions, and exact budget boundaries.

The host suite contains 80 deterministic generated programs plus 27 directed
cases. Both Node and Wasmtime agree with a separate named-variable interpreter.
The directed cases cover integer encoding boundaries, overflowing addition,
large sections and local indices, closure capture, and multiple entry arguments.
Wasmtime's module cache is disabled so validation does not require writes to a
global cache directory. Its signed CLI values are converted to u32 bit patterns.

Additional e2e assertions check that proof-bearing, proof-free, and dependent
increment programs emit identical binaries; the proof-bearing and proof-free
programs also emit identical runtime IR. Invalid proofs, erased uses, malformed
syntax, and budget exhaustion do not create or alter the requested output.
The CLI rejects attempts to overwrite its source through the same path, a path
alias, a symlink, or a hardlink, and reports missing input/output directory errors.

## Initial performance evidence

Command: `opam exec -- python3 -P scripts/bench.py`.
One warmup and seven samples per case, fresh compiler processes and fresh output
files, warm OS caches. Times include process startup, parsing, checking, erasure,
lowering, binary emission, and file I/O. No proof cache exists in M0.

| Arithmetic leaves | Plain source median | Proof-bearing median | OCaml native object median |
| --- | ---: | ---: | ---: |
| 32 | 5.029 ms | 4.645 ms | 41.368 ms |
| 256 | 5.332 ms | 5.396 ms | 49.000 ms |
| 1024 | 7.471 ms | 11.637 ms | 80.514 ms |

The workloads compute equivalent modular int32 arithmetic. Every proof-bearing
leaf adds an erased reflexivity obligation. Proof-bearing and plain Wasm outputs
are byte-identical. The harness independently runs the generated OCaml and Wasm
programs outside the timed region and compares them to an arithmetic oracle.

The checked-in [raw snapshot](m0-benchmark.json) contains all timing samples,
input hashes, compiler hash, and environment. A rerun writes a new result to
`artifacts/bench/results.json` and does not replace this historical snapshot.

This is a microbenchmark with different output backends: Wasm module versus
native object. It does not establish OCaml-speed compilation for agent
applications, module graphs, or arbitrary dependent proofs. M0 has no incremental
artifact cache, effects, dynamic validators, GC object runtime, or host APIs.
No semantic preservation theorem has been mechanized.
