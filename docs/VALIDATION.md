# Compiler validation, 2026-09-06

## M1 finite dependent pairs and validated budgets, 2026-09-06

Implemented on base commit `e372ac6` in an isolated workspace checkout.

```text
opam exec -- dunecho build
  OK build: 0 errors, 0 warnings
_build/default/test/kernel_test.exe
  kernel: 356 cases, 0 failures
node scripts/e2e.mjs
  e2e: 1585 programs, 3170 host executions, erasure and rejection checks passed
bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

The 53 new kernel cases cover finite Sigma formation, annotated construction,
dependent second projection, nested abstract evidence, ghost and runtime phases,
malformed families before conversion, and inactive sum alternatives. They check
both component scopes, outer-name shadowing, direct AST substitution under
Sigma and refinement binders, and a stuck evidence conditional with an outer
index. Closed projections reduce while open projections remain distinct.
Product and Sigma types do not convert implicitly. Scalar exports, erased uses,
bare proof fields, and function fields retain explicit rejection behavior.

The fixed dependent conditional in `sigma_budget_source` compiles in exactly
405 steps and rejects fuel 404. The actual validated-budget example compiles
to 236 bytes in 1901 steps; fuel 1900 is rejected without changing an existing
output. Its check-only count is 1750. The existing example compilation pins
remain 366/365 for refined-increment, 468/467 for budget-sum, 1411/1410 for
record-policy, and 501/500 for validated-ceiling. These boundaries were measured
with the new binary, including output preservation on fuel exhaustion.

The host suite adds 389 programs. The independent evaluator uses a tagged
dependent pair with two eager components, separate from ordinary product
arrays. Directed tests cover both projections, unsigned boundaries, nested
Sigma/record/sum layouts, conditional and case results, closure arguments and
repeated calls, erased outer captures, transport, and checked branch evidence.
Thirty generated dependent programs augment the mixed generator. Seven pairs
of product and Sigma programs have identical IR and Wasm, including nested
inactive alternatives. Three Sigma fixtures execute at exactly 50,000 combined
parameters and locals; their one-over counterparts are rejected. CLI malformed
forms, invalid types and evidence, reserved binders, and erased uses preserve
existing outputs and create no absent artifacts.

The strengthened constructor-shadowing fixture runs across nine inputs in
the full run. Its 18 host executions are part of the 3170 total.

The actual validated-budget file runs for 216 combinations of spent, proposed,
ceiling, and field selector. An independent oracle uses exact JavaScript
addition to distinguish overflow, an exceeded ceiling, and successful totals.
This covers accepted zero separately from failure through the status selector,
the signed boundary, maximum u32, and a wrapped total that fits the ceiling.

Eight targeted mutations in a separate scratch tree all compiled and were
rejected by semantic kernel regressions: wrong Sigma family depth, a phantom
constructor binder, wrong construction substitution, wrong second-projection
substitution, checking either component in Ghost, skipping family formation,
and dropping the second inactive zero-fill shape. None relied only on the
fixed fuel assertion. Independent core and documentation reviews found no
concrete correctness defect. No benchmark was refreshed or mechanized
preservation claim added. The dependent data representation remains finite
and internal, and the public ABI remains integers.

## M1 named records, 2026-09-06

Implemented over `a754ce3` plus the staged checked-branch-evidence slice, in an
isolated workspace checkout. The earlier staged changes are preserved.

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 303 cases, 0 failures
  e2e: 1196 programs, 2392 host executions, erasure and rejection checks passed
bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

The 69 new kernel cases cover ordered record identity, empty and duplicate
fields, missing projections, finite payload restrictions, erased-field misuse,
open and closed conversion, outer indices, substitution, refinement erasure,
transport, checked branches, direct AST validation, and exact fuel exhaustion.
They include regressions for neutral value/evidence projections through record
fields and for rejecting pair projections on records. Three cases pin the
label-specific parse diagnostic, one contrasts it with the binder diagnostic,
and two pin the order that reports an empty or duplicate label before a field
error. Four cases pin two contradictory if-proof nests, one over the same
condition and one over a convertible condition, with their exact erased IR.
Four cases call the backend on hand-built runtime terms to reach the
conditional label mismatch, the conditional length mismatch, the field
projection of a non-record, and the lookup of an absent field. Five further
cases check negative and out-of-scope locals, negative and overflowing u32
constants, and negative arity through the public runtime constructor. These
malformed inputs return explicit errors before indexing or serialization.

The fixed fuel boundaries were re-measured with the final binary. Run
`_build/default/bin/main.exe --fuel N compile EXAMPLE OUT` at N and at N-1.
`examples/refined-increment.aw` accepts at 366 and rejects at 365.
`examples/budget-sum.aw` accepts at 468 and rejects at 467.
`examples/record-policy.aw` accepts at 1411 and rejects at 1410.
`examples/validated-ceiling.aw` accepts at 501 and rejects at 500.
`main.exe check` reports 348, 341, 1277, and 440 steps for the same four
examples, in that order. The boundaries 332/331 and 217/216 that earlier
sections state were measured before later M1 slices added budget ticks, so
they no longer hold.

Record leaves count toward the backend limit of 50,000 parameters and locals.
A conditional record spends one local for the condition, one local for each
branch leaf that needs a computation, one merge local for each leaf of the
result record, and one local for the branch effects. A leaf that is a literal
or a bound variable needs no computation local. The first fixture gives every
field its own addition, in the shape `(export main (fn (run x u32) (field (if
(u32-lt x 100) (record (f0 (add x 0)) ...) (record (f0 (add x 1)) ...)) f1)))`.
With one parameter this costs 1 + 3N + 3 parameters and locals, so N = 16665
compiles to 617144 bytes and N = 16666 gives the backend error `function
exceeds 50000 parameters and locals`. The second fixture gives every field a
plain bound variable, the leaf shape of `examples/record-policy.aw`, and costs
1 + N + 2, so N = 49997 compiles to 683518 bytes and N = 49998 gives the same
backend error. Both boundaries were measured with a fuel limit above the step
cost of the fixture. This is an accepted tradeoff of the local
representation, not a defect.

The independent evaluator uses named Maps for records, with eager construction
and explicit field lookup. The 136 added programs cover the actual record-policy
example, all field positions, closures, nested records, refined fields, records
inside sums, and product/sum fields inside conditional records. The mixed random
generator also produces records. Both hosts agree with the independent results.
Local-limit fixtures retain computations from unselected fields. Twenty-one new
CLI rejection forms, reserved-label checks, and local-limit rejections preserve
existing output files and create no absent artifacts. Each record and branch
rejection asserts its exact diagnostic, so no other guard can mask it. The two
empty-record entries stay inside a u32-typed export, because a record-typed
export is rejected first.

Independent static reviews covered the core, runtime, evaluator, and example.
Incomplete constructor matches found during development were corrected before
the successful build; review found no remaining confirmed defect. No benchmark
was refreshed or mechanized soundness claim added. Records remain internal
finite data, with ordered fields and no dependent field binders or object ABI.

## M1 checked branch evidence, 2026-09-06

Implemented on base commit `a754ce3` in an isolated workspace checkout.

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 234 cases, 0 failures
  e2e: 1060 programs, 2120 host executions, erasure and rejection checks passed
bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

The 26 new kernel cases cover both evidence polarities, runtime proof rejection,
condition phases, result formation and outer indices, unreachable branch
checking, closed and stuck conversion, nested capture, parser scopes, exact
fuel exhaustion, and identical IR/Wasm after evidence erasure. This slice did
not change the fixed fuel boundaries. The values 332/331 for refinements and
217/216 for sums were measured before later M1 slices added budget ticks. The
current pins are 366/365 for `examples/refined-increment.aw` and 468/467 for
`examples/budget-sum.aw`. Run
`_build/default/bin/main.exe --fuel N compile EXAMPLE OUT` at N and at N-1 to
reproduce them.

The independent interpreter binds a witness for the selected boolean outcome.
The 94 new programs cover the actual ceiling validator across unsigned
boundaries, all three comparison operators, refined success and failure sums,
nested branches and closures, and 30 generated conditional validators. Ten
additional CLI rejections preserve existing artifacts and create no absent
outputs. The public Wasm ABI remains integer-only.

Five targeted mutations all built and were rejected by the kernel tests:
wrong true polarity, wrong false polarity, missing result-type shift, missing
branch-binder traversal depth, and missing erased scope entry. The result-shift
mutation initially survived the kernel suite but failed the ceiling host
fixture; a dedicated outer-index kernel regression now rejects it as well.
Sources were restored and the full suite rerun after the mutations.

No benchmark was refreshed or mechanized soundness claim added. The validator
proves only its checked comparison; u32 addition still requires explicit
overflow validation.

## M1 refined values, 2026-09-06

Implemented on base commit `9b5b400` in an isolated workspace checkout:

```text
opam exec -- dunecho build
  OK build: 0 errors, 0 warnings
_build/default/test/kernel_test.exe
  kernel: 208 cases, 0 failures
node scripts/e2e.mjs
  e2e: 966 programs, 1932 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

The 47 new kernel cases cover refinement formation, dependent proof checking,
runtime payload and ghost evidence phases, projection conversion, nested binder
substitution, transport through refinement and sum families, export rejection,
and malformed families hidden in sum alternatives or case result annotations.
One malformed case family has an ill-typed endpoint that normalizes to a valid
one, pinning formation before conversion. The earlier unpinned case-handler
substitution depth now has a stuck-scrutinee capture regression and a rejected
wrong-endpoint twin. Three further cases pin the inactive-alternative zero
fill for a refined product, transport of a refined value in the Execute phase,
and a stuck value projection under a conditional.

A fixed refinement-returning case compiles in exactly 332 steps and rejects
fuel 331. Recursive checks of sum alternatives and case result annotations,
with new budget ticks in runtime type and type normalization, add 35 steps to
the earlier fixed sum fixture: it now accepts at 217 and rejects at 216. These
are intentional shared-budget changes. The numbers 332/331 and 217/216 are the
measurement of this slice. Later M1 slices added more budget ticks: the current
pins are 366/365 and 468/467.

The independent named-variable interpreter represents refinements as packages
containing a value and proof, distinct from the erased scalar/product runtime
representation. Directed and generated programs exercise nested refinements,
booleans, products, sums, both branches, closure arguments and repeated calls,
outer indices, erased captures, and transported families. The actual example
runs across seven u32 boundaries and matches an exact modular-increment oracle.
Its IR and Wasm bytes match a plain let-bound increment. A refined 50,000-local
fixture matches its plain counterpart byte for byte; 50,001 locals are rejected.
CLI rejections preserve existing artifacts and create no absent outputs.

Six targeted mutations in an isolated source copy all built and were rejected
by kernel regressions: removing case-handler or refinement-family binder depth,
checking a runtime payload in Ghost,
adding a phantom erasure binder, substituting
the package instead of its value into projected evidence, and omitting case
result formation. The scratch sources were restored. Independent core review
found no correctness defect and supplied the stronger case-formation detector.

No benchmark was refreshed or mechanized soundness claim added. Comparisons
still do not construct branch evidence or establish overflow freedom.

## M1 internal sums, 2026-09-06

Implemented on base commit `d1077d2` in an isolated workspace checkout:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 161 cases, 0 failures
  e2e: 858 programs, 1716 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

The 32 new kernel cases cover injection typing, both case handlers, scalar-only
export restrictions, nested payload restrictions, erased uses, binder scope,
closed and open conversion, substitution capture, transport, and ghost erasure.
A fixed product-returning case with a sum-valued scrutinee compiles in exactly
182 shared steps and rejects fuel 181. This pins sum shape traversal, branch
checking, erasure, merging, and emission together.

The independent named-variable interpreter represents sums as tagged objects.
Generated programs now include sum conditionals and case binders. Directed
programs cover nested heterogeneous sums, product and boolean case results,
sum-returning cases, closure arguments, repeated applications, and outer runtime
captures separated by erased binders. The actual budget-sum example runs for
216 combinations against exact JavaScript arithmetic. Both hosts execute case
and sum-conditional fixtures at 50,000 locals; corresponding 50,001-local
programs are rejected. CLI malformed sums, type errors, reserved handler names,
and erased uses preserve existing outputs and create no absent outputs.

No benchmark was refreshed, and no mechanized preservation claim is made.

## M1 product conditionals, 2026-09-06

Implemented on base commit `2fddd85`, product conditionals and budget-result:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 129 cases, 0 failures
  e2e: 605 programs, 1210 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny <absolute lib, bin, test paths>
  no obligations at or above medium in 14 files
git diff --check
  clean
```

New cases cover nested mixed scalar products, branch-local computations, erased
binder remapping, both selections, mismatched fields and shapes, function and
ghost evidence field rejection, closed conversion, and exact compilation fuel.
The host suite checks 216 budget-result inputs against exact JS addition,
12 nested product programs against the independent interpreter, and a product
conditional at exactly 50,000 locals. One additional local is rejected while
preserving output artifacts. The previously unpinned normalization of a stuck
transport's value now has a kernel regression. Earlier benchmark snapshots below
are historical and were not refreshed for this slice.

## Original M0 validation

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

## M1 boolean predicates and budget policy, 2026-09-06

Validated in the workspace copy:

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 91 cases, 0 failures
  e2e: 331 programs, 662 host executions, erasure and rejection checks passed
```

Seven added kernel cases cover boolean conditional composition, conversion,
dependent substitution, mismatched branches, export restrictions, erased use
in an unreachable boolean branch, and matching product-branch rejection. Five differential programs exercise nested boolean branches and
use their results repeatedly with branch-local computations.

The actual budget-policy file executes on both hosts for 108 combinations of
spent, proposed, and ceiling. An independent oracle uses exact JavaScript number
addition over the two u32 inputs, without reproducing the modular overflow test.
Cases include zero, exact ceilings, maximum u32, and sums crossing both the
signed boundary and the u32 limit. Existing local-limit and erasure checks pass.
No new benchmark or mechanized preservation claim accompanies this slice.

## M1 equality transport, 2026-09-06

```text
sh scripts/check.sh
  OK build: 0 errors, 0 warnings
  kernel: 120 cases, 0 failures
  e2e: 376 programs, 752 host executions, erasure and rejection checks passed

bagrep obligations --include-tests --deny lib bin test
  no obligations at or above medium in 14 files

git diff --check
  clean
```

The 29 new kernel cases cover abstract symmetry and transitivity, dependent
function families, scalar/product erasure, ghost endpoints and proofs, both
endpoint substitutions, type formation, runtime evidence restrictions, reserved
binders, capture under a family and nested function binder, open transport
conversion, computed reflexivity, and exact shared-budget exhaustion.

Both hosts execute the symmetry example, transported closures with captured
values, and transported pairs across five u32 boundaries. Another 30 generated
programs place transported computations in executable branches. The independent
interpreter gives transport the runtime semantics of its value. The symmetry
example's IR and binary match plain increment. New CLI rejections preserve
existing artifacts and do not create absent outputs.

Seven targeted mutations were tested in an isolated source copy. All built and
all were rejected by kernel regressions: checking the wrong proof endpoint,
substituting the wrong source or target endpoint, checking runtime values in the
ghost phase, omitting the family binder during substitution, reducing transport
with an open proof, and inserting a phantom binder during erasure. Original
sources were restored before final validation. This is regression evidence,
not a mechanized soundness proof.

The benchmark now includes transport around every arithmetic leaf, alongside
plain and erased-proof sources at 32, 256, and 1024 leaves. All three variants
emit identical Wasm bytes and execute against the arithmetic oracle. The
[transport benchmark snapshot](m1-transport-benchmark.json) records seven samples,
source and compiler hashes, environment, output sizes, and the OCaml comparison.
These process-level microbenchmarks do not establish application-scale speed.

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
