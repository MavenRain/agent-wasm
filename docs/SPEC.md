# M0 compiler specification

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
type    ::= u32 | (eq term term) | (pi (rel name type) type)
term    ::= integer | name
          | (add term term)
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
Addition is modulo 2^32 in
both conversion and Wasm execution. These are machine integers, not natural
numbers suitable for unchecked budget arithmetic.

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
program type is private and contains only constants, locals, addition, functions,
calls, and lets. It has no source type or proof constructors.

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
