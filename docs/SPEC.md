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
type    ::= u32 | bool | (product type type) | (sum type type)
          | (record (label type) ...)
          | (refine (name type) type)
          | (eq term term) | (pi (rel name type) type)
term    ::= integer | true | false | name
          | (add term term)
          | (pair term term) | (fst term) | (snd term)
          | (record (label term) ...) | (field term label)
          | (inl type term) | (inr type term)
          | (case type term (name term) (name term))
          | (pack type term term) | (value term) | (evidence term)
          | (u32-eq term term) | (u32-lt term term) | (u32-le term term)
          | (if term term term)
          | (if-proof type term (name term) (name term))
          | (fn (rel name type) term)
          | (app rel term term)
          | (let (rel name type) term term)
          | (refl term)
          | (transport (name type) term term term term)
          | (ann term type)
```

Semicolon comments run to the end of the line. Binding is lexical; shadowing is
allowed. Names elaborate to de Bruijn indices, including occurrences in types.
Integer literals use one or more ASCII decimal digits and range from 0 through
4294967295. Leading zeros are allowed. Signs, separators, and base prefixes are
rejected. Tokens starting with a digit or sign are reserved for literals and
cannot be used as binder names in functions, dependent function types, lets,
transport families, refinement families, or case and evidence handlers.
Record labels follow the same lexical restriction, but do not bind names.
The boolean literals `true` and `false` are also reserved binder names.
Addition is modulo 2^32 in
both conversion and Wasm execution. These are machine integers, not natural
numbers suitable for unchecked budget arithmetic.

## M1 scalar validation slice

`bool` is distinct from `u32`. The three comparisons accept u32 operands and
return bool, using unsigned equality, less-than, and less-than-or-equal. There
are no implicit integer/boolean conversions. `if` requires a bool condition and
two branches of the same type: u32, bool, or nested products, records, sums,
and refinements of those types. Both branches are checked in the enclosing
phase, including an unreachable branch. At runtime the condition is evaluated
first and only the selected branch executes. Function and runtime evidence
fields are not supported in conditional results. Refinement evidence is checked
and erased. Internal functions and lets bind booleans; the export ABI remains
exclusively `u32 -> ... -> u32`.

Conversion reduces closed comparisons and selects a branch when the normalized
condition is a boolean literal. For an open condition it normalizes both branches
without equating them or using an arithmetic solver. Equality evidence remains
indexed exclusively by u32 terms, which may now contain conditionals. A comparison
does not itself construct equality evidence or refine the checking context.

Erasure lowers boolean literals to canonical i32 values 0 and 1, preserves runtime
comparisons and conditions, and deletes erased boolean bindings in the same way
as other ghost values. Code generation emits `i32.eq`, `i32.lt_u`, `i32.le_u`, and
result-valued Wasm `if`/`else` blocks. Each comparison and scalar conditional receives a
local, as does addition. Locals from both branches count toward the combined
50,000 limit and have distinct indices; their instructions remain inside their
respective branches. Static expansion and serialization charge both branches
against the compilation budget even though execution chooses only one.

A product conditional executes its selected branch's bindings once in an initial
Wasm conditional with a dummy scalar result. It then selects each scalar leaf
with an empty-binding conditional using the original condition. This allocates
one local for branch execution plus one per leaf, with no heap object or ABI
change. Selection reads only the selected branch's locals. Recursive type checks
and field merging charge the shared budget; all generated locals count toward
the same limit. Products containing functions remain available outside conditional
results.

`examples/price-ceiling.aw` returns 1 when an input price is at most 100, else 0.
It uses no arithmetic on amounts. This is an executable predicate, not yet the
planned validator proving its acceptance condition. Named records, general
dependent pairs, and non-wrapping amount operations remain future M1 work.

## M1 refined values

`(refine (x A) P)` is a dependent pair with a runtime payload of type A and
an erased equality proof of P. A has a finite shape built from u32, bool,
products, records, sums, and refinements. Functions and bare equality evidence
are excluded from its payload. P must be an `eq` type, well formed under the
erased binder `x : A`. A is outside that binder. This is a restricted form
of dependent pair, not a general Sigma type or an implicit refinement solver.

`(pack R value proof)` requires an explicit refinement type R. The payload
is checked in the enclosing phase against A, and the proof is checked in
the ghost phase against P with `value` substituted for x. Neither term is
inside the refinement binder. Incorrect evidence is rejected even when the
package or an enclosing branch will be erased or unselected.

`(value package)` returns its payload type, checking the package in the
enclosing phase. `(evidence package)` is available only in the ghost phase:
it checks the package there and returns P with `(value package)` substituted
for x. An erased package cannot supply a runtime payload. Retrieving evidence
does not unfold an abstract package or identify its value with an index by
definitional conversion; explicit transport can use the projected proof.

Conversion normalizes package annotations, values, and proofs. A value or
evidence projection of a normalized pack selects the corresponding term;
projections of open packages remain symbolic with normalized operands. There
is no pair eta rule or proof irrelevance. Mapping and substitution traverse
the proof family under its payload binder and constructor arguments in their
original scope. Transport can rewrite equality indices inside refinements,
including under sums, without changing runtime shape.

Refinements are admitted in runtime products, records, sums, conditionals, and
case results. Each sum alternative and the explicit case result are checked for
well-formed indexed evidence as well as supported runtime shape. A case result
is outside both handler binders and is shifted under each of them.
The export ABI remains exclusively `u32 -> ... -> u32`.

Erasure keeps only a pack's payload. The value projection erases to its
operand, with no added binder, instruction, local, or runtime wrapper. An
inactive sum alternative with a refined type stores only the zero-filled
payload shape; it constructs no proof. Only checked terms enter erasure,
and an evidence projection encountered at runtime is rejected. All formation,
substitution, normalization, and erasure work shares the compilation budget.

`examples/refined-increment.aw` packages the modular increment with evidence
that its payload equals `(add n 1)`, retrieves that evidence in a ghost binding,
and returns the payload. Its IR and Wasm match the equivalent plain let-bound
increment. Ordinary comparisons and conditionals do not introduce equality
proofs. The explicit `if-proof` form described below supplies checked branch
evidence for executable refinement. Named records support structured results;
general dependent pairs remain M1 work.

## M1 internal sums

`(sum A B)` is a non-dependent tagged choice. Both payload types must be built
from u32, bool, products, records, sums, and refinements, in either phase.
Functions and bare equality evidence are excluded, even in an inactive
alternative. Refinement families are checked in both alternatives.
`(inl B value)` infers `(sum A B)` from `value : A`; `(inr A value)` infers it
from `value : B`. The explicit type describes the other alternative. Injection
evaluates its payload eagerly and checks it in the enclosing phase.

`(case R value (left a) (right b))` requires `value : (sum A B)` and checks
both handlers against the explicit result type R, with `left : A` and
`right : B` bound separately. R is outside the payload binders and must also
be built from scalar, product, record, sum, and refinement types. Both handlers
are checked in the enclosing phase, including unreachable handlers. This is
non-dependent elimination: selecting an alternative does not introduce equality
evidence. The export ABI still excludes sums and their payloads as structured
values.

Conversion normalizes the scrutinee. A known injection substitutes its payload
into the corresponding handler and normalizes that body. An open scrutinee
remains a symbolic case with normalized result type and handlers. Mapping and
substitution traverse each handler under its own binder.

Erasure lowers a sum to `(pair tag (pair left right))`, using tag 1 for left
and 0 for right. The inactive payload is recursively zero-filled according to
its finite scalar shape; nested inactive sums use tag 1. No source type or
evidence remains in the runtime IR. Case lowering binds the scrutinee once,
then branches on its tag and binds only the selected payload for its handler.
The extra scrutinee binder is accounted for when remapping outer variables.
Existing product conditionals select the tag and both payload slots together.
Only the selected branch's instructions execute. Compilation still expands
both branches, including inactive storage, under the shared fuel/local limits.
This representation uses no heap allocation and is internal to this compiler.

`examples/budget-sum.aw` returns an internal `(sum u32 u32)`: left 1 for
overflow, left 2 for exceeding the ceiling, or right with the accepted total.
A final case adapts it to the scalar ABI: field 0 returns status, any other
field returns the successful total or zero on error. Named error variants remain
future work. Refinements can carry separately checked evidence.

## M1 product slice

`(product A B)` is a non-dependent pair type. `(pair a b)` infers its two
component types; `fst` and `snd` require a product and return the corresponding
component. Components may be scalars, nested products, or internal functions.
Both components are checked in the enclosing phase, even when only one is
projected. Runtime products cannot contain bare equality evidence, including
inside nested products; refinement fields keep only their payload at runtime.
Ghost products may contain proofs and disappear when bound
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
limits. The integer export ABI is unchanged; finite product shapes also support
conditional results as described above.
This representation relies on static shapes and the pure, terminating fragment;
it is not a general object ABI.

`examples/tool-policy.aw` packages a tool identifier and price as a pair and
checks the immutable allowlist {7, 9} and price ceiling 100. It returns 1 or 0,
uses no amount arithmetic, and supplies no host authority or refined evidence.
Named records and general dependent pairs remain future work.

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

## M1 equality transport

`(transport (index FAMILY) from to proof value)` binds `index : u32` only in
`FAMILY`, with erased relevance. Both endpoints must have type u32 in the ghost
phase, and `proof` must have type `(eq from to)` in that phase. The family must
be well formed in the context extended by its index. The checker substitutes
`from` into the family and checks `value` against that type in the enclosing
phase, then returns the family with `to` substituted. Substitution removes the
family binder and lifts replacements under any nested binders.

Transport is available in both phases. Transporting an erased variable into a
runtime position is rejected, as is returning equality evidence at runtime.
The family may contain products or dependent functions, subject to the usual
formation and relevance rules. It cannot branch on its index to select a type:
indices occur in equality propositions, so transport never changes runtime
representation. This restriction is essential to the erasure rule.

Conversion first normalizes the proof. When it becomes `refl`, transport reduces
to its normalized value. Otherwise it normalizes the family, endpoints, and
value and retains a symbolic transport, even for equal endpoints. There is no
proof irrelevance or rule equating all proofs. Only checked terms enter this
conversion path; endpoint agreement has already been established by checking.

Erasure deletes the family, endpoints, and proof and recursively erases only
the value, in the unchanged surrounding scope. The family binder introduces
no runtime variable. There is no transport constructor in the runtime IR and
no extra Wasm instruction or local. Checking and normalization still charge
the shared compilation budget for ghost work.

Transport supports abstract equality symmetry and transitivity without axioms.
`examples/transport.aw` defines symmetry in a ghost binding and produces the
same IR and Wasm as plain increment. Transport consumes evidence, including
projections from refined values. Comparisons still do not produce proofs or
refine branches. Evidence-bearing executable validation remains future work.

## Checking

The type fragment has dependent products and equality indexed by u32 terms.
It has no universe, arbitrary inductive family, recursion,
propositional extensionality, or user axioms. Reflexivity, definitional conversion,
and explicit equality transport construct equality evidence. This is a dependent
fragment, not a general theorem prover.

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
automatic rewriting is provided. Explicit transport consumes a checked equality
proof and reduces on reflexive evidence. In particular, symbolic `add x 0` is not
definitionally equal to `x`. Function parameter annotations and let annotations
are explicit.

The public entry type must be `u32 -> ... -> u32`, with zero or more runtime
parameters. Internal higher-order functions are allowed within the finite,
statically expandable fragment. Higher-order exports are rejected.

## Erasure and code generation

Only an abstract `Kernel.checked` value can enter the erasure API. The erased
program type is private and contains only constants, locals, addition, comparisons,
conditionals, pairs, projections, functions, calls, and lets.
It has no source type or proof constructors.

Erasure deletes erased binders and their values or arguments, removes annotations
and transport wrappers, and remaps surviving variables. A proof encountered at a runtime position is an
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

## M1 evidence-bearing conditionals

`(if-proof RESULT CONDITION (yes THEN) (no ELSE))` checks CONDITION as bool
in the enclosing phase. RESULT is a well-formed finite branch type, checked
outside both binders, with the same payload restrictions as case results.
THEN and ELSE are both checked against RESULT lifted under one erased binder.
The yes binder has type `(eq (if CONDITION 1 0) 1)`; the no binder has type
`(eq (if CONDITION 1 0) 0)`. Each binder is scoped only over its own branch.
Existing names can be shadowed, subject to the usual literal-name restriction.

Evidence may construct a refined payload or feed erased arguments and transport.
It cannot be read at runtime or appear in the result type through a free branch
binder. A runtime condition cannot read erased data. Ghost uses may inspect
ghost conditions, but their computations are erased. Ordinary `if` retains its
existing behavior and introduces no evidence.

Conversion normalizes the condition. A literal bool selects its branch and
substitutes `(refl 1)` or `(refl 0)` for the evidence binder, then normalizes
the result. An open condition leaves an `if-proof` with normalized result type
and branches. There is no general branch-assumption rewriting or commuting
conversion through projections. Traversal counts both branch binders for
capture-avoiding substitution and shares the existing checking budget.

The evidence describes the normal form of the condition. An if-proof nested in
the opposite branch of an earlier one, over the same condition or a convertible
condition, holds both evidence polarities in one context. Such a context proves
`(eq 0 1)`, so the inner branch can build any refined value. That branch is
dead at runtime, because the erased `if` tests the same condition. A program
that reaches the contradiction never executes it. Conversion must therefore
stay a subrelation of the erased evaluator. This is a soundness assumption for
evidence-bearing conditionals, not only a completeness property. The kernel
suite pins both nests and their erased IR.

Erasure drops each evidence binder and lowers to the existing runtime `If`.
The condition executes once and only the selected branch executes. Proofs add
no runtime slots, tags, or locals. The integer export ABI is unchanged.
`examples/validated-ceiling.aw` demonstrates an error/refined-value sum whose
successful payload proves its unsigned comparison succeeded. This does not
establish non-wrapping arithmetic or policy validity beyond that comparison.

## M1 named records

`(record (tool u32) (price u32))` is a structural record type.
`(record (tool 7) (price 75))` constructs a record, and `(field action price)`
selects a field. Type and value syntax are distinguished by position. Records
must be nonempty and labels must be unique; duplicate, empty, and missing-field
errors are explicit. Labels and their declaration order participate in type
identity. Reordering fields requires explicit reconstruction. There is no
width subtyping, implicit coercion, record update, or empty-record unit type.

Record fields support u32, bool, and finite products, sums, refinements, and
records. Raw equality evidence and functions cannot be record fields. A
refinement's evidence is still permitted and erased. Field declarations bind
no variables: field types may reference outer indices but cannot depend on
other fields. General dependent pairs remain separate future work. All field
values are checked in the enclosing phase and evaluated eagerly in declaration
order, including fields that are not subsequently selected.

Conversion normalizes every field and projects a known record by label. A
projection of an open record stays symbolic; different labels remain distinct.
Records can be branch results, sum payloads, refinement payloads, and internal
function arguments. Formation checks recurse through every field. Mapping,
formation, normalization, lookup, and backend field traversal share the budget.

The runtime IR retains labels for static selection, but Wasm contains only
the scalar computations. Branch effects execute once before selecting fields;
all emitted locals count toward the existing portability limit. Record exports
and entry parameters remain unsupported by the integer ABI. The record-policy
example validates tool IDs 7 or 9 and a price no greater than 100, packages the
accepted record with erased evidence, then returns price plus 1 or rejection 0.
The ceiling ensures this particular adapter addition cannot overflow.

## Future boundary rule

An untrusted model or network response must pass an executable validator before
receiving a refined type. Validator code, policy data, keys, amounts, freshness
checks, and executable authority survive erasure. Only logical evidence can be
erased. Host imports must expose their authority and trust assumptions explicitly.
The design must account for revocation and concurrent state changes separately
from proofs about immutable snapshots.
