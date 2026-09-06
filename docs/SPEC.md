# Compiler specification

## Accepted direction

The project targets WebAssembly. OCaml is the compiler implementation language.
The long-term language is an eager ML-family language with dependent contracts,
checked erasure, explicit errors, effects, ownership, and structured concurrency.
Its workloads come from the [Built in Venice directory](https://builtinvenice.ai/).
No vendor API credentials or remote services are needed for M0.

M0 emits the core Wasm integer subset. Managed objects will require a later
representation decision, with WasmGC the proposed direction. M0's integer ABI
does not commit the project to a linear-memory object runtime or a Component
Model ABI. Native and JavaScript code generation are outside the target plan;
JavaScript currently only hosts the emitted Wasm.

## Syntax

```text
program ::= (export main term)
rel     ::= run | erase
type    ::= u32 | bool | (product type type)
          | (eq term term) | (pi (rel name type) type)
term    ::= integer | true | false | name
          | (add term term)
          | (pair term term) | (fst term) | (snd term)
          | (u32-eq term term) | (u32-lt term term) | (u32-le term term)
          | (if term term term)
          | (fn (rel name type) term)
          | (app rel term term)
          | (let (rel name type) term term)
          | (refl term)
          | (ann term type)
```

Semicolon comments run to the end of the line. Binding is lexical; shadowing is
allowed. Names elaborate to de Bruijn indices, including occurrences in types.
Integer literals use one or more ASCII decimal digits and range from 0 through
4294967295. Leading zeros are allowed. Signs, separators, and base prefixes are
rejected. Tokens starting with a digit or sign are reserved for literals and
cannot be used as binder names in functions, products, or lets.
The boolean literals `true` and `false` are also reserved binder names.
Addition is modulo 2^32 in
both conversion and Wasm execution. These are machine integers, not natural
numbers suitable for unchecked budget arithmetic.

## M1 scalar validation slice

`bool` is distinct from `u32`. The three comparisons accept u32 operands and
return bool, using unsigned equality, less-than, and less-than-or-equal. There
are no implicit integer/boolean conversions. `if` requires a bool condition and
two branches of the same scalar type, either u32 or bool. Both branches are
checked in the enclosing phase, including an unreachable branch. At runtime
the condition is evaluated first and only
the selected branch executes. Function-valued and product-valued branches are
not supported in this slice. Internal functions and lets can bind booleans;
the export ABI remains exclusively `u32 -> ... -> u32`.

Conversion reduces closed comparisons and selects a branch when the normalized
condition is a boolean literal. For an open condition it normalizes both branches
without equating them or using an arithmetic solver. Equality evidence remains
indexed exclusively by u32 terms, which may now contain conditionals. A comparison
does not itself construct equality evidence or refine the checking context.

Erasure lowers boolean literals to canonical i32 values 0 and 1, preserves runtime
comparisons and conditions, and deletes erased boolean bindings in the same way
as other ghost values. Code generation emits `i32.eq`, `i32.lt_u`, `i32.le_u`, and
result-valued Wasm `if`/`else` blocks. Each comparison and conditional receives a
local, as does addition. Locals from both branches count toward the combined
50,000 limit and have distinct indices; their instructions remain inside their
respective branches. Static expansion and serialization charge both branches
against the compilation budget even though execution chooses only one.

`examples/price-ceiling.aw` returns 1 when an input price is at most 100, else 0.
It uses no arithmetic on amounts. This is an executable predicate, not yet the
planned validator returning a sum with erased evidence. Sums, records, dependent
pairs, transport, and non-wrapping amount operations remain future M1 work.

## M1 product slice

`(product A B)` is a non-dependent pair type. `(pair a b)` infers its two
component types; `fst` and `snd` require a product and return the corresponding
component. Components may be scalars, nested products, or internal functions.
Both components are checked in the enclosing phase, even when only one is
projected. Runtime products cannot contain equality evidence, including inside
nested products. Ghost products may contain proofs and disappear when bound
with `erase`; projecting an erased product at runtime is rejected.

Evaluation constructs pairs eagerly, first the left component, then the right.
Projection evaluates the whole operand before selecting a field. Conversion
normalizes both components and reduces projections of normalized pairs.
Open projections remain symbolic. Product components introduce no binder, so
indices in either component refer to the same surrounding context. There is no
pair eta rule and the second component cannot depend on the first.

The erased IR preserves pairs and projections without type or proof data. Static
expansion represents a pair as two compiler values, retaining scalar instructions
from both fields in evaluation order, including an unselected field. Pair
construction and projection consume compilation budget but allocate no Wasm
object or extra local of their own. Field computations still count toward local
limits. The integer export ABI is unchanged; conditional results remain scalar.
This representation relies on static shapes and the pure, terminating fragment;
it is not a general object ABI.

`examples/tool-policy.aw` packages a tool identifier and price as a pair and
checks the immutable allowlist {7, 9} and price ceiling 100. It returns 1 or 0,
uses no amount arithmetic, and supplies no host authority or refined evidence.
Named records, sums, dependent pairs, and transport remain future work.

## M1 budget policy

Boolean-valued conditionals compose predicates without converting through u32.
Their typing, conversion, erasure, and branch evaluation follow the scalar rules
above, and they use the existing i32 branch representation.

`examples/budget-policy.aw` accepts spent, proposed, and ceiling as u32 inputs.
It returns 1 exactly when the mathematical sum of spent and proposed is at most
ceiling. It first computes the modular total, then returns false if total is
less than spent; otherwise it checks total against ceiling. For two u32 inputs,
an overflowing sum wraps exactly once and its wrapped value is strictly less
than spent. This detects overflow even when the wrapped value fits the ceiling.
The source `add` operation remains modular. The example reports a decision,
without distinguishing overflow from an exceeded ceiling or constructing erased
evidence. Structured validation errors remain future work.

## Checking

The type fragment has dependent products and equality indexed by u32 terms.
It has no universe, arbitrary inductive family, recursion, equality eliminator,
propositional extensionality, or user axioms. Only reflexivity and definitional
conversion construct equality evidence. This is a dependent fragment, not a
general theorem prover.

Checking uses an execution phase and a ghost phase. In the execution phase,
erased variables cannot be referenced and equality evidence cannot be returned.
An erased argument or let value is checked in the ghost phase. Type indices are
checked in the ghost phase as u32 expressions. Runtime equality domains are
rejected. Ordinary lambda bodies are checked in the enclosing phase even when
the lambda's own argument is erased: erasing an argument does not grant its
body permission to use that argument at runtime.

For application, the argument must match the product's domain and relevance.
Substitution into the codomain removes that binder and lifts the argument under
remaining binders. For a let, its annotation and value are checked, then its body
is checked with an abstract binding, and its inferred result type is substituted.
The bound value is not unfolded in the local context during body checking.

Conversion normalizes beta applications, explicit lets, annotations, and closed
u32 addition, then compares syntax. No eta rule, arithmetic solver, or general
rewriting is provided. In particular, symbolic `add x 0` is not definitionally
equal to `x`. Function parameter annotations and let annotations are explicit.

The public entry type must be `u32 -> ... -> u32`, with zero or more runtime
parameters. Internal higher-order functions are allowed within the finite,
statically expandable fragment. Higher-order exports are rejected.

## Erasure and code generation

Only an abstract `Kernel.checked` value can enter the erasure API. The erased
program type is private and contains only constants, locals, addition, comparisons,
conditionals, functions, calls, and lets. It has no source type or proof constructors.

Erasure deletes erased binders and their values or arguments, removes annotations,
and remaps surviving variables. A proof encountered at a runtime position is an
error even after checking. Code generation sees only the erased program.

The backend expands static closures with lexical environments, converts each
runtime addition to an i32 local assignment, and emits a binary module with type,
function, export, and code sections. Runtime arithmetic is not evaluated by the
compiler. Binary encoding follows the core Wasm
[module](https://webassembly.github.io/spec/core/binary/modules.html) and
[instruction](https://webassembly.github.io/spec/core/binary/instructions.html)
formats. There are no host imports or implicit capabilities.

Static closure expansion is an M0 restriction and can increase compile work and
code size. It must be replaced or supplemented before recursion, effects, general
closures, or separate compilation. Erased lambda removal currently relies on the
source fragment being pure and terminating.

## Work limits and trusted code

The default shared budget is 1,000,000 steps. Parsing, elaboration, checking,
substitution, normalization, erasure, static closure expansion, and emitted local
assignments consume steps. `--fuel N` selects a positive budget. Exhaustion is an
error and does not produce output. It never admits an unchecked obligation.

The parser caps source length at 1 MiB and nesting at 128. Tokenization, name
lookup, structural comparison, allocation, diagnostics, and byte serialization
are not individually charged. A step is not a wall-clock or memory bound. Input
is currently read before the parser applies its size limit. Library callers that
construct ASTs directly bypass parser size and depth limits.

The backend caps the combined count of entry parameters and generated locals at
50,000, with a separate cap of 1,000 entry parameters. These limits also apply
to direct AST clients. Exceeding either compiler portability limit is a backend
error, even with increased fuel, and does not create or replace the output file.

Trusted components include the hand-written checker, erasure, backend, OCaml
toolchain/runtime, Wasm engine, and host runner. The kernel and erasure have
regression and differential tests but no mechanized preservation proof yet.
No claim of complete privacy enforcement, effect safety, or financial policy
safety is made by this pure milestone.

## Future boundary rule

An untrusted model or network response must pass an executable validator before
receiving a refined type. Validator code, policy data, keys, amounts, freshness
checks, and executable authority survive erasure. Only logical evidence can be
erased. Host imports must expose their authority and trust assumptions explicitly.
The design must account for revocation and concurrent state changes separately
from proofs about immutable snapshots.
