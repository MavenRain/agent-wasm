import AgentWasm.DependentContexts

open AgentWasm
open AgentWasm.Finite
open AgentWasm.Dependent

namespace DependentContextTest

abbrev C := Dependent.Context
abbrev I := Indexed.Ty

def empty : C 0 := .nil
def one : C 1 := .snoc empty (.base .u32)
def evidence : C 2 := .snoc one (.eq (.var 0) (.uint 7))
def mixed : C 3 := .snoc evidence (.base .bool)

def refinement : I 3 := .refine .u32 (.var 0) (.var 3)
def refined : C 4 := .snoc mixed refinement
def sigma : I 4 :=
  .sigma .bool (.refine .u32 (.var 0) (.cond (.var 1) (.var 5) (.var 0)))
def telescope : C 5 := .snoc refined sigma

-- Lookup moves a declaration past itself and every newer context entry.
example : lookup evidence 0 = .eq (.var 1) (.uint 7) := rfl
example : lookup mixed 1 = .eq (.var 2) (.uint 7) := rfl
example : lookup telescope 3 = .eq (.var 4) (.uint 7) := rfl
example : lookup telescope 4 = .base .u32 := rfl
example : lookup telescope 2 = .base .bool := rfl
example : lookup telescope 1 = .refine .u32 (.var 0) (.var 5) := rfl
example : lookup telescope 0 =
    .sigma .bool (.refine .u32 (.var 0)
      (.cond (.var 1) (.var 6) (.var 0))) := rfl

-- Omitting the declaration's own shift makes its endpoint refer to itself.
example : lookup evidence 0 ≠ .eq (.var 0) (.uint 7) :=
  fun h => Nat.noConfusion
    (congrArg Fin.val (Term.var.inj (Indexed.Ty.eq.inj h).1))

example : lookup telescope 3 ≠ .eq (.var 3) (.uint 7) :=
  fun h => (show (4 : Nat) ≠ 3 from of_decide_eq_true rfl)
    (congrArg Fin.val (Term.var.inj (Indexed.Ty.eq.inj h).1))

theorem one_formed : Dependent.Context.WellFormed one := .snoc .nil .base
theorem evidence_formed : Dependent.Context.WellFormed evidence :=
  .snoc one_formed (.eq (.var rfl) .uint)
theorem mixed_formed : Dependent.Context.WellFormed mixed :=
  .snoc evidence_formed .base
theorem refinement_formed : Dependent.WellFormed mixed refinement :=
  .refine (.var rfl) (.var rfl)
theorem refined_formed : Dependent.Context.WellFormed refined :=
  .snoc mixed_formed refinement_formed
theorem sigma_formed : Dependent.WellFormed refined sigma :=
  .sigma True.intro
    (.refine (.var rfl) (.cond (.var rfl) (.var rfl) (.var rfl)))
theorem telescope_formed : Dependent.Context.WellFormed telescope :=
  .snoc refined_formed sigma_formed

example : Dependent.WellFormed telescope (lookup telescope 3) :=
  telescope_formed.lookup 3
example : Dependent.WellFormed telescope (lookup telescope 1) :=
  telescope_formed.lookup 1
example : Dependent.WellFormed telescope (lookup telescope 0) :=
  telescope_formed.lookup 0

example : IndexHasType telescope (.var 4) .u32 := .var rfl
example : IndexHasType telescope (.var 2) .bool := .var rfl
example : IndexHasType telescope (.cmp .lt (.var 4) (.uint 8)) .bool :=
  .cmp (.var rfl) .uint
example : IndexHasType telescope
    (.ann (.snd (.pair (.boolean true) (.var 4))) .u32) .u32 :=
  .ann (.snd (.pair .boolean (.var rfl)))

-- Representation shape does not authorize an implicit refinement elimination.
example : Indexed.shape (lookup telescope 1) = some .u32 := rfl
example : ¬ IndexHasType telescope (.var 1) .u32 :=
  fun h => match h with
    | .var hlookup => nomatch hlookup

example : ¬ IndexHasType telescope (.var 3) .u32 :=
  fun h => match h with
    | .var hlookup => nomatch hlookup

example : Indexed.shape (lookup telescope 0) = some (.product .bool .u32) := rfl
example : ¬ IndexHasType telescope (.var 0) (.product .bool .u32) :=
  fun h => match h with
    | .var hlookup => nomatch hlookup

example : ¬ IndexHasType telescope (.snd (.var 0)) .u32 :=
  fun h => match h with
    | .snd (.var hlookup) => nomatch hlookup

example : ¬ IndexHasType telescope (.fst (.var 0)) .bool :=
  fun h => match h with
    | .fst (.var hlookup) => nomatch hlookup

example : ¬ Dependent.WellFormed telescope (.eq (.var 1) (.uint 0)) :=
  fun h => match h with
    | .eq (.var hlookup) (_hr) => nomatch hlookup

example : ¬ Dependent.WellFormed telescope (.eq (.uint 0) (.var 3)) :=
  fun h => match h with
    | .eq (_hl) (.var hlookup) => nomatch hlookup

example : ¬ Dependent.Context.WellFormed
    (.snoc telescope (.eq (.snd (.var 0)) (.uint 0))) :=
  fun h => match h with
    | .snoc (_hΓ) (.eq (.snd (.var hlookup)) (_hr)) => nomatch hlookup

example : ¬ Dependent.Context.WellFormed
    (.snoc refined (.refine .u32 (.var 0) (.var 1))) :=
  fun h => match h with
    | .snoc (_hΓ) (.refine (_hl) (.var hlookup)) => nomatch hlookup

-- Branch results still reject equality evidence in a dependent context.
example : ¬ Dependent.WellFormed telescope
    (.sum (.eq (.var 4) (.uint 7)) (.base .u32)) :=
  fun h => match h with
    | .sum ha (_hb) (_wa) (_wb) => ha

example : ¬ Dependent.WellFormed telescope
    (.sigma .u32 (.product (.base .bool) (.eq (.var 0) (.var 5)))) :=
  fun h => match h with
    | .sigma hb (_wb) => hb.2

def boundTerm : Term 5 :=
  .letIn .u32 (.var 4)
    (.case .u32 (.inl .bool (.var 0))
      (.add (.var 0) (.var 6)) (.var 6))

theorem boundTerm_typed : IndexHasType telescope boundTerm .u32 :=
  .letIn (.var rfl)
    (.case (.inl (.var rfl)) (.add (.var rfl) (.var rfl)) (.var rfl))

example : rename Fin.succ boundTerm =
    .letIn .u32 (.var 5)
      (.case .u32 (.inl .bool (.var 0))
        (.add (.var 0) (.var 7)) (.var 7)) := rfl

example : IndexHasType (.snoc telescope (.eq (.var 4) (.uint 7)))
    (rename Fin.succ boundTerm) .u32 :=
  boundTerm_typed.weaken (.eq (.var 4) (.uint 7))

example : Dependent.WellFormed (.snoc refined (.eq (.var 3) (.uint 7)))
    (Indexed.rename Fin.succ sigma) :=
  sigma_formed.weaken (.eq (.var 3) (.uint 7))

-- A nonuniform open renaming skips dependent entries in the target telescope.
def source : C 2 := .snoc one (.base .bool)
def intoTelescope : Renaming 2 5 :=
  Fin.cases 2 (Fin.cases 4 Fin.elim0)

theorem intoTelescope_preserves :
    Dependent.RenamingPreserves source telescope intoTelescope :=
  Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))

def boundSchema : I 2 :=
  .sigma .bool (.refine .u32
    (.letIn .u32 (.var 3) (.add (.var 0) (.var 4)))
    (.cond (.var 2) (.var 0) (.var 3)))

theorem boundSchema_formed : Dependent.WellFormed source boundSchema :=
  .sigma True.intro (.refine
    (.letIn (.var rfl) (.add (.var rfl) (.var rfl)))
    (.cond (.var rfl) (.var rfl) (.var rfl)))

example : Indexed.rename intoTelescope boundSchema =
    .sigma .bool (.refine .u32
      (.letIn .u32 (.var 6) (.add (.var 0) (.var 7)))
      (.cond (.var 4) (.var 0) (.var 6))) := rfl

example : Dependent.WellFormed telescope
    (Indexed.rename intoTelescope boundSchema) :=
  boundSchema_formed.rename intoTelescope intoTelescope_preserves

def openTerm : Term 2 :=
  .letIn .bool (.var 0)
    (.case .u32 (.inr .u32 (.var 0)) (.add (.var 0) (.var 3))
      (.cond (.var 0) (.var 3) (.var 3)))

theorem openTerm_typed : IndexHasType source openTerm .u32 :=
  .letIn (.var rfl) (.case (.inr (.var rfl))
    (.add (.var rfl) (.var rfl)) (.cond (.var rfl) (.var rfl) (.var rfl)))

example : rename intoTelescope openTerm =
    .letIn .bool (.var 2)
      (.case .u32 (.inr .u32 (.var 0)) (.add (.var 0) (.var 6))
        (.cond (.var 0) (.var 6) (.var 6))) := rfl

example : IndexHasType telescope (rename intoTelescope openTerm) .u32 :=
  openTerm_typed.rename intoTelescope intoTelescope_preserves

#print axioms Dependent.rename_weaken
#print axioms Dependent.liftRen_preserves
#print axioms Dependent.IndexHasType.rename
#print axioms Dependent.IndexHasType.weaken
#print axioms Dependent.WellFormed.rename
#print axioms Dependent.WellFormed.weaken
#print axioms Dependent.Context.WellFormed.lookup

end DependentContextTest
