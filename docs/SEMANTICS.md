# Finite core semantics and proof obligations

This document specifies the current finite core at base `e0a500e`. It gives
rules to audit against `lib/ast.ml`, `lib/kernel.ml`, and `lib/erase.ml`.
The rules and obligations below are not a mechanized soundness proof.
The [Lean binding library](MECHANIZATION.md) proves typed substitution
results over intrinsically scoped terms, including phase access for a
non-dependent subset and erased context binder removal. It also proves
formation-preserving substitution for indexed type schemas over finite
contexts, with binding composition laws. Its exact boundary is stated
separately. The full dependent obligations below remain open.
The [syntax specification](SPEC.md) defines the concrete forms and limits.

## Contexts, phases, and substitution

Write `G |-p t : A` for checking against `A`, up to conversion, in phase
`p`, either `Execute` or `Ghost`. Inference computes a type representative.
A context entry is `x :r A`, where relevance `r` is `run` or `erase`.
Types in context entries are stored in the context before their own binder.
At de Bruijn index `k`, lookup therefore lifts the stored type by `k + 1`.
`WF(G, A)` means type formation. Every type index is checked in `Ghost`.
Names below abbreviate capture-avoiding de Bruijn syntax, not global names.

`B[a/x]` removes the binder for `x`, replacing its occurrences with `a`.
At local binder depth `d`, index `d` becomes `a` lifted by `d`; indices
greater than `d` decrease by one, and smaller indices are unchanged.
The replacement is in the surrounding context, outside the removed binder.
Shifting changes only free indices, starting at depth zero. Negative indices
and shifts that move a free index below the current depth are errors.

| Form | Children under one additional binder |
| --- | --- |
| `pi (r x A) B`, `sigma (x A) B`, `refine (x A) P` | Only `B` or `P` |
| `fn (r x A) t` | Only `t` |
| `let (r x A) a t` | Only `t` |
| `case R s (x a) (y b)` | `a` and `b`, separately |
| `if-proof R c (yes a) (no b)` | `a` and `b`, separately |
| `transport (x B) a b p v` | Only `B` |
| All other forms, including `dpair`, `pack`, and records | None |

The domain, complete constructor annotation, case result, conditional result,
and transport endpoints remain in their original context. Nested type and
term binders compose, including binders inside equality endpoints.

## Type formation and conversion

Define finite shapes `F` by u32, bool, products of finite shapes, Sigma pairs
of finite shapes, nonempty ordered records of finite shapes, sums of finite
shapes, and refinements with a finite payload. This shape predicate ignores
equality indices, but formation must check them separately. Bare equality
and functions are not finite shapes.

Define runtime-admissible types `D`: u32, bool, any formed Pi, products,
Sigma pairs, records, and sums with runtime-admissible components, and
refinements with runtime-admissible payloads. Bare equality is excluded.
Formation further restricts Sigma, record, sum, and refinement payloads to
finite shapes. Products may contain functions and, in `Ghost`, bare proofs.

Formation rules are:

| Type | Premises |
| --- | --- |
| `u32`, `bool` | None |
| `product A B` | `WF(G,A)` and `WF(G,B)` |
| `eq a b` | `G |-Ghost a : u32` and `G |-Ghost b : u32` |
| `pi (r x A) B` | `WF(G,A)`, `WF(G,x :r A,B)`; if `r=run`, `D(A)` |
| `sigma (x A) B` | Finite `A,B`; `WF(G,A)` and `WF(G,x :erase A,B)` |
| `refine (x A) P` | Finite formed `A`; form equality `P` under `x :erase A` |
| `sum A B` | `F(A)`, `F(B)`, `WF(G,A)`, `WF(G,B)` |
| `record (l_i A_i)` | Nonempty, unique labels; each field finite and formed |

Field declarations do not bind names. Record label order is part of type
identity. Runtime domain checks also apply to lambdas in the ghost phase.

`A == B` means their normal forms are syntactically equal. Normalization
recurses through surviving types and terms, including proof terms.
It reduces beta applications, lets, annotations, closed modular addition and
comparisons, known pair/record/refinement projections, and known sum cases.
A known `if` selects a branch. A known `if-proof` substitutes `refl 1` or
`refl 0` into its selected branch. Transport normalizes its proof first and
reduces to its normalized value only when that proof becomes `refl`.
Discarded children need not normalize: annotations and let declarations are
removed, known cases and proof conditionals discard their result annotations,
and reflexive transport discards its family and endpoints.

An unresolved eliminator stays symbolic with normalized children. An open
transport retains its normalized family, endpoints, proof, and value.
Lambda bodies are normalized, as are both branches of an unresolved
conditional or case. No eta, proof irrelevance, arithmetic solver, or
projection-through-conditional commuting rule is included. Products and
Sigma types do not convert to one another. Normalization is a checking
procedure and is distinct from the eager evaluation relation below.

## Typing rules

Every successful inference in `Execute` also requires `D` of its
result. Checking `t` against `A` infers `B` and requires `B == A`.
Explicit annotations are formed before they are used for checking.
Let `arg(p,run)=p` and `arg(p,erase)=Ghost`.

- `x`: look up its lifted type. In `Execute`, its relevance must be `run`.
- Integer `n`: require `0 <= n < 2^32`; result `u32`.
  `true` and `false` have type `bool`.
- `add a b`: both operands at `p` have type `u32`; result `u32`.
  `u32-eq`, `u32-lt`, and `u32-le` have the same premises and return `bool`.
- `fn (r x A) t`: form `A`, require `D(A)` if `r=run`, and infer `B`
  for `t` in `G,x :r A` at `p`. Result: `pi (r x A) B`.
- `app r f a`: at `p`, require `f : pi (r x A) B`; at `arg(p,r)`,
  check `a : A`. Result: `B[a/x]`.
- `let (r x A) a t`: form `A`; check `a : A` at `arg(p,r)`; infer `B`
  for `t` in `G,x :r A` at `p`. Result: `B[a/x]`.
- `ann t A`: form `A` and check `t : A` at `p`. Result: `A`.
- `pair a b`: infer `A`, `B` for both operands at `p`.
  Result: `product A B`.
- `dpair S a b`: form `S = sigma (x A) B`; check `a : A` and
  `b : B[a/x]` at `p`. Result: `S`.
- `fst t`: at `p`, require `t : product A B` or `sigma (x A) B`.
  Result: `A`.
- `snd t`: at `p`, `t : product A B` gives result `B`, while
  `t : sigma (x A) B` gives result `B[(fst t)/x]`.
- `record (l_i t_i)`: check nonempty unique labels, infer each `A_i` at
  `p`, require `F(A_i)`, and form each `A_i`. Result: ordered record type.
- `field t l`: infer the complete record operand at `p` and return the
  declared type for `l`.
- `inl B a` and `inr A b`: infer the active payload at `p`; form the
  complete sum, including its inactive type. Result: `sum A B`.
- `case R s (x a) (y b)`: form finite `R`; infer `s : sum A B` at `p`;
  check handlers against lifted `R` in `G,x :run A` and `G,y :run B` at
  `p`. Result: `R`.
- `if c a b`: check `c : bool` at `p`; infer finite `A` for `a` at `p`;
  check `b : A` at `p`. Result: `A`.
- `pack R a q`: form `R = refine (x A) P`; check `a : A` at `p` and
  `q : P[a/x]` in `Ghost`. Result: `R`.
- `value t`: at `p`, require `t : refine (x A) P`. Result: `A`.
- `evidence t`: only in `Ghost`, infer `t : refine (x A) P`.
  Result: `P[(value t)/x]`.
- `refl t`: check `t : u32` in `Ghost`. Result: `eq t t`, hence excluded
  in `Execute`.
- `transport (x B) a b q v`: check u32 endpoints and `q : eq a b` in
  `Ghost`; form `B` in `G,x :erase u32`; check `v : B[a/x]` at `p`.
  Result: `B[b/x]`.

For `if-proof R c (yes a) (no b)`, form finite `R` and check `c : bool`
at `p`. Put `I(c) = if c 1 0`. Check `a` against lifted `R` at `p` in
`G,yes :erase (eq I(c) 1)`, and `b` against lifted `R` at `p` in
`G,no :erase (eq I(c) 0)`. The result is `R` in `G`; neither evidence
binder may escape. Both branches are checked even when `c` is closed.

Let bodies use abstract bindings; the checker does not unfold their values
inside the context. An erased lambda parameter does not change the phase of
its body. A runtime let has no separate `D(A)` formation premise, but using
its proof-valued right-hand side in `Execute` fails the result check.

A public program is closed and inferred in `Execute`. Its type must be zero
or more `pi (run x u32)` binders ending in `u32`. Backend parameter and local
limits are subsequent compilation checks, not extra typing rules.

## Evaluation

Write `rho |- t => v` for successful evaluation in a lexical environment.
Values are u32s, booleans, ordered records, products, dependent pairs,
left/right injections, refinement packages, equality witnesses, and lexical
closures. Types have no rule in this relation. Erasure, not evaluation, uses
a type to build the inactive sum payload. This mathematical relation is
defined on well-typed terms under environments that satisfy their dependent
types and evidence assumptions.

Variables read `rho`; literals are values. `add` evaluates both operands
left to right and returns `(a+b) mod 2^32`. Comparisons use unsigned operands.
Pairs, dependent pairs, and record fields evaluate eagerly, left to right.
Injections evaluate their active payload. Projections evaluate their whole
operand before selecting a component. A package evaluates its payload and
its proof, and `value`/`evidence` select from an evaluated package.
`refl t` evaluates `t` to its u32 witness.

`fn (r x A) t` returns a closure with the current environment. Application
evaluates the function and argument, then evaluates the closure body with
its captured environment extended by the argument. This relation evaluates
both relevances; erasure later removes ghost arguments. A let evaluates its
value and then its body in the extended environment, for either relevance.
An annotation evaluates its term. Transport evaluates its payload and
returns it; its endpoints, family, and evidence are checked statically.

For `if`, evaluate `c` and then exactly the selected branch. For `case`,
evaluate the sum and then exactly the matching handler with its active
payload bound. For `if-proof`, evaluate `c` once and then exactly the
selected branch with equality witness 1 or 0 bound. This witness realizes
the branch assumption because `I(c)` has the corresponding value in `rho`.
No evaluation rule executes an unselected branch.

The named-variable interpreter in `scripts/e2e.mjs` implements this evaluation
strategy for its test corpus, without using compiler substitution or Wasm
lowering. Its proof objects are witnesses, not runtime proof verifiers.
It does not establish that every well-typed term terminates or that its
environment satisfies all type indices. Those are separate obligations.

## Erasure relation and runtime representation

Write `E_s^d(t)` for erasure with source scope `s` and runtime binder depth
`d`. Scope entries, newest first, are either erased or a runtime level `l`.
A surviving variable becomes runtime index `d-l-1`; an erased variable at a
runtime occurrence is an error. The initial scope is empty with depth zero.

Define zero-fill `Z(A)` on finite shapes: scalar zero; componentwise pairs
for products and Sigma; ordered componentwise records; payload zero for
refinements; and `(pair 1 (pair Z(A) Z(B)))` for `sum A B`. These inactive
values are storage placeholders, not inhabitants of their source refinements.
The value relation only constrains the active sum payload.

| Source | Runtime erasure |
| --- | --- |
| u32 literal | Same constant |
| bool literal | Constant 1 or 0 |
| Arithmetic, comparisons, ordinary `if` | Same operator on erased operands |
| `pair a b`, `dpair S a b` | Pair of erased components |
| Projections, records, and field selection | Corresponding runtime form |
| `pack R a q`, `value a` | Erasure of `a` |
| `transport (x B) a b q v`, `ann v A` | Erasure of `v` |
| `fn (run x A) t` | `Fn E(t)` with runtime level `d` in scope, depth `d+1` |
| `fn (erase x A) t` | `E(t)` with erased scope entry, depth unchanged |
| `app run f a` | `Call E(f) E(a)` |
| `app erase f a` | `E(f)` |
| `let (run x A) a t` | `Let E(a) E(t)`; level `d` and depth `d+1` for body |
| `let (erase x A) a t` | `E(t)` with erased scope entry, depth unchanged |
| `inl B a` | `Pair 1 (Pair E(a) Z(B))` |
| `inr A b` | `Pair 0 (Pair Z(A) E(b))` |
| `if-proof R c (yes a) (no b)` | `If E(c) E(a) E(b)`; ghost branch binders |
| `refl`, `evidence` at a surviving occurrence | Error |

Case erasure introduces a runtime scrutinee binding with no source binder:

```text
Let E(s)
  (If (Fst (Local 0))
    (Let (Fst (Snd (Local 0))) E(a))
    (Let (Snd (Snd (Local 0))) E(b)))
```

Each handler is erased with source scope `Some(d+1) :: s` and runtime depth
`d+2`. Thus its payload is local 0 and an outer runtime variable skips both
new runtime bindings. This differs from the source's single handler binder.
Each `if-proof` branch instead adds one erased source entry with no change
to runtime depth.

The erased evaluator is eager with lexical closures and the same unsigned
arithmetic. Products and records contain values. `If` chooses one branch
using canonical bool constants. The backend statically expands closures and
structures, then emits scalar instructions; this is an additional compilation
pass, not the definition of erasure. Compilation expands both branches, while
Wasm execution evaluates one. See SPEC for field selection and local limits.

## Obligations and executable evidence

These are proof targets, with their assumptions stated explicitly:

1. **Binding algebra.** Lifting and substitution preserve scope and avoid
   capture across every binder in the table. Removing an unused fresh binder
   after lifting recovers the original syntax. Substitution composition must
   account for lifting an open replacement under nested term and type binders.
2. **Typed substitution.** Given a well-formed context and formed types,
   `G,x :r A |-p t : B` and a replacement
   `G |-arg(p,r) a : A`, substituting into the term and type preserves typing
   in `G`. Substitution through a context suffix must also substitute into
   each dependent entry; omitting that suffix is not a general theorem.
3. **Shape invariance.** Substitution in a formed type preserves its type
   constructors, relevance, and ordered labels, changing only terms in
   equality indices. Runtime-admissible source and target instantiations of a
   transport family therefore share a representation. Ghost-only equality
   families have no runtime representation. Prove this over formation,
   including nested Sigma and refinement families.
4. **Conversion adequacy.** Convertible, well-typed u32 terms evaluate to
   the same integer under any environment realizing their context. A proof
   of this fact must cover open transport and evidence-bearing branches.
   Equal normal forms alone do not prove it for the implementation.
5. **Preservation and branch realization.** Evaluation preserves dependent
   typing, and a selected `if-proof` arm receives valid evidence. Contexts
   containing both polarities for the same condition may be inconsistent.
   Such branches must be unreachable under a realizing environment; arbitrary
   symbolic evidence contexts cannot be treated as runtime inputs.
6. **Erasure simulation.** For a well-typed Execute term and related source
   and runtime environments, successful source evaluation is related to
   evaluation of its erasure. Relate booleans to 0/1, refinements to payloads,
   Sigma to products, sums by active tags/payloads, and records fieldwise.
   Relate runtime functions extensionally on related arguments. An erased
   function relates to the same erased computation for every admissible ghost
   argument. This requires an irrelevance argument, not pairwise syntax
   equality of arbitrary source functions.
7. **Termination and backend simulation.** Establish termination for the
   supported typed fragment and correctness of static closure expansion and
   binary emission. Erased lambda removal can expose a body before source
   application, so purity and termination are necessary. A future extension
   with recursion or effects must revisit this rule.

Budgets bound compiler traversal steps and can reject an otherwise well-typed
program. The obligations above concern successful checks and translations,
with sufficient resources. They do not equate fuel use across substitution
or erasure and do not claim that the step budget bounds time or memory.

`test/binding_test.ml` supplies executable checks of binding algebra against
an independent named representation. These concern syntax, including scoped
but untyped terms. The kernel suite checks accepting and rejecting typed
examples. The host suite compares source evaluation with Node and Wasmtime,
including proof erasure and contradictory dead branches. These checks provide
regression evidence for parts of the obligations, not universal proofs.

Mechanization should first cover scope and typed substitution, then conversion
adequacy and branch realization, then the value relation and erasure simulation.
No milestone should be called verified until its claimed fragment and trusted
backend boundary have corresponding completed proofs.
