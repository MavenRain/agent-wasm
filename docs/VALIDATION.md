# Compiler validation, 2026-09-06

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

## M0 hardening follow-up, 2026-09-06

After bounding backend locals and specifying decimal-only literal syntax:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 34 cases, 0 failures
  e2e: 116 programs, 232 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny lib bin test
  no obligations at or above medium in 14 files
```

Both hosts execute programs at the 50,000 combined parameter/local limit,
including a case with one runtime parameter. The suite rejects one-over-limit
programs with and without a parameter, plus the original 65,536-leaf reproducer,
using increased fuel. Each rejection preserves an existing artifact and creates
no new artifact. Argument-selection cases distinguish all three entry parameters,
also with an intervening erased proof binder. Literal cases cover leading zeros,
non-decimal syntax, signed syntax, separators, and values beyond both u32 and i64.

## M0 boundary and state follow-up, 2026-09-06

After enforcing the separate parameter cap, validating binder names, and
threading immutable backend state:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 38 cases, 0 failures
  e2e: 118 programs, 236 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny lib bin test
  no obligations at or above medium in 14 files

git diff --check
  clean
```

Direct AST tests accept 1,000 entry parameters and reject 1,001 through checking,
erasure, and emission, without depending on the parser's depth cap. These are
library tests; the host suite exercises source programs within the parser limit.
Binder regressions cover functions, lets, and product types, including unused
names beginning with decimal digits or signs. CLI rejection preserves existing
output and creates no new artifact. A valid hyphenated name remains accepted.

Two new differential programs exercise arithmetic in a function-producing let,
a call argument, and a closure body, plus arithmetic before entry parameters
are applied. Existing local-limit, parameter-order, budget, and erasure checks
also pass with explicitly threaded state.

## M1 scalar validation slice, 2026-09-06

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 55 cases, 0 failures
  e2e: 201 programs, 402 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny <absolute-lib> <absolute-bin> <absolute-test>
  no obligations at or above medium in 14 files

git diff --check
  clean
```

Kernel additions cover boolean typing and export restrictions, both branches
being checked, erased conditions and dead-branch erased uses, conditional
conversion in equality indices, dependent substitution, and proof erasure.
Boolean literal names are rejected in all three binder forms.

The named-variable interpreter now evaluates comparisons and conditionals. The
80 generated cases include nested conditional expressions. Directed tests cover
all 25 pairs of 0, 1, 2147483647, 2147483648, and 4294967295 for each comparison,
boolean closure arguments, branch-local calculations used afterward, and prices
on both sides of the example ceiling. Both hosts execute a conditional at the
50,000-local boundary, with locals split across both branches. One additional
local is rejected without creating or altering output. Invalid conditions and
branches likewise preserve output. No new mechanized proof is claimed.

The existing arithmetic benchmark also completed, including its independent
runtime checks and proof-erasure byte comparison. Medians in milliseconds:

| Leaves | Plain | Proof-bearing | OCaml native object |
| --- | ---: | ---: | ---: |
| 32 | 6.003 | 5.698 | 49.804 |
| 256 | 13.214 | 18.829 | 70.220 |
| 1024 | 7.696 | 11.602 | 87.867 |

The [raw slice snapshot](m1-scalar-benchmark.json) records the full samples.
These timings are higher than the initial snapshot in most cells, particularly
at 256 leaves. This single run does not isolate compiler changes from machine
variation and is not a performance gate. It measures the existing arithmetic
corpus, not validator application performance.

## M1 product slice, 2026-09-06

Validated in an isolated workspace copy with the same OCaml toolchain:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 84 cases, 0 failures
  e2e: 218 programs, 436 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny <absolute-lib> <absolute-bin> <absolute-test>
  no obligations at or above medium in 14 files
```

The 29 new kernel cases cover products, projections, type mismatch, export
restrictions, nested proof-field rejection, ghost proof products, projection
conversion, dependent argument substitution, product type indices, capture,
and erased index remapping. Two cases distinguish strict from inclusive
comparison at equal operands during conversion, closing the scalar review gap.
One case puts evidence in the first component of a runtime product domain.
Three cases keep open projections symbolic: a proof of `(eq (fst p) (snd p))`
by `(refl (fst p))` is rejected, a proof of `(eq (fst (snd p)) (snd (fst p)))`
by `(refl (snd (fst p)))` is rejected, and the reflexive form is accepted. One case
calls the checker without erasure, so the enclosing-phase rule on an
unselected field is pinned by the kernel alone.

The independent interpreter and deterministic generator now include pairs and
projections. Directed programs exercise both projections, state retained across
both fields, branch-local pairs, closure fields with captured computations,
pair arguments and results, nesting, booleans, and work before entry parameters.
Five cases compile the actual tool-policy example and compare both hosts with
a separate scalar policy oracle, including allowlist misses, the exact ceiling,
one above the ceiling, and maximum u32. Rejections retain existing output and
create no new output. Backend limit tests count work in unselected fields and
across both fields of a pair. No new performance measurement or mechanized
preservation claim accompanies this slice.

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
