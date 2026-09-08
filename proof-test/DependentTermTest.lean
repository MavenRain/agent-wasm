import AgentWasm.DependentTerms

open AgentWasm
open AgentWasm.Finite.Phased
open AgentWasm.Dependent

namespace DependentTermTest

abbrev H {n : Nat} := @Dependent.HasType n

def empty : Dependent.Context 0 := .nil
def one : Dependent.Context 1 := .snoc empty (.base .u32)
def emptyQ : Quantities 0 := Fin.elim0
def runtime : Quantities 1 := extendWith emptyQ .run
def erased : Quantities 1 := extendWith emptyQ .erase
def evidence : Dependent.Context 2 := .snoc one (.eq (.var 0) (.uint 7))
def evidenceQ : Quantities 2 := extendWith runtime .erase

theorem evidence_ghost :
    H .ghost evidence evidenceQ (.var 0) (.eq (.var 1) (.uint 7)) :=
  .var (.eq (.var rfl) .uint) True.intro True.intro

example : ¬ H .execute evidence evidenceQ (.var 0)
    (.eq (.var 1) (.uint 7)) := Dependent.erased_var_rejected rfl

-- Runtime relevance cannot expose an equality as an Execute value.
example : ¬ H .execute evidence (extendWith runtime .run) (.var 0)
    (.eq (.var 1) (.uint 7)) := execute_equality_rejected

example : H .ghost one erased (.var 0) (.base .u32) :=
  .var .base True.intro True.intro

example : ¬ H .execute one erased (.var 0) (.base .u32) :=
  Dependent.erased_var_rejected rfl

example : H .ghost one erased (.refl (.var 0)) (.eq (.var 0) (.var 0)) :=
  .refl (.var rfl)

example : ¬ H .execute one runtime (.refl (.var 0))
    (.eq (.var 0) (.var 0)) := execute_equality_rejected

example : ¬ H .ghost empty emptyQ (.refl (.boolean true))
    (.eq (.boolean true) (.boolean true)) :=
  fun h => match h with
    | .refl hi => nomatch hi

example : ¬ H .ghost empty emptyQ (.refl (.uint 7))
    (.eq (.uint 7) (.uint 8)) := fun h => nomatch h

def checkedPayload : Dependent.Term 2 :=
  .pack .u32 (.var 0) (.uint 7) (.var 1) (.var 0)

-- The payload executes while its exact dependent equality uses the erased slot.
theorem checkedPayload_typed : H .execute evidence evidenceQ checkedPayload
    (.refine .u32 (.var 0) (.uint 7)) :=
  .pack (.refine (.var rfl) .uint) (.var rfl) True.intro evidence_ghost

example : H .execute evidence evidenceQ (.value checkedPayload) (.base .u32) :=
  .value checkedPayload_typed

example : ¬ H .execute empty emptyQ
    (.pack .u32 (.var 0) (.uint 8) (.uint 7) (.refl (.uint 7)))
    (.refine .u32 (.var 0) (.uint 8)) :=
  fun h => match h with
    | .pack (_ha) (_hv) (_hq) hh => nomatch hh

example : ¬ H .execute one erased
    (.pack .u32 (.var 0) (.var 0) (.var 0) (.refl (.var 0)))
    (.refine .u32 (.var 0) (.var 0)) :=
  fun h => match h with
    | .pack (_ha) (_hv) hq (_hh) => hq

-- The packed payload must have the finite domain of its refinement.
example : ¬ H .execute empty emptyQ
    (.pack .u32 (.uint 7) (.uint 7) (.boolean true) (.refl (.uint 7)))
    (.refine .u32 (.uint 7) (.uint 7)) :=
  fun h => match h with
    | .pack (_ha) hv (_hq) (_hh) => nomatch hv

def sigmaFamily : Indexed.Ty 1 := .refine .u32 (.var 0) (.var 1)
def badFam : Indexed.Ty 1 := .base .u32
def dependentPair : Dependent.Term 0 :=
  .dpair .u32 sigmaFamily (.uint 7)
    (.pack .u32 (.var 0) (.uint 7) (.uint 7) (.refl (.uint 7)))

example : Indexed.instantiate sigmaFamily (.uint 7 : Finite.Term 0) =
    .refine .u32 (.var 0) (.uint 7) := rfl

theorem dependentPair_typed : H .execute empty emptyQ dependentPair
    (.sigma .u32 sigmaFamily) :=
  .dpair (.sigma True.intro (.refine (.var rfl) (.var rfl))) .uint True.intro
    (.pack (.refine (.var rfl) .uint) .uint True.intro (.refl .uint))

example : H .execute empty emptyQ (.dfst dependentPair) (.base .u32) :=
  .dfst dependentPair_typed

-- The second component must use the actual first component in its schema.
example : ¬ H .execute empty emptyQ
    (.dpair .u32 sigmaFamily (.uint 7)
      (.pack .u32 (.var 0) (.uint 8) (.uint 8) (.refl (.uint 8))))
    (.sigma .u32 sigmaFamily) :=
  fun h => match h with
    | .dpair (_ha) (_hv) (_hq) ht => nomatch ht

example : ¬ H .execute empty emptyQ
    (.dpair .u32 sigmaFamily (.uint 7) (.finite (.uint 7)))
    (.sigma .u32 sigmaFamily) :=
  fun h => match h with
    | .dpair (_ha) (_hv) (_hq) ht => nomatch ht

-- The Sigma witness must have the finite domain of its schema.
example : ¬ H .execute empty emptyQ
    (.dpair .u32 badFam (.boolean true) (.finite (.uint 7)))
    (.sigma .u32 badFam) :=
  fun h => match h with
    | .dpair (_ha) hv (_hq) (_ht) => nomatch hv

-- Both product components are checked even when a projection discards one.
example : ¬ H .execute one erased
    (.fst (.pair (.finite (.uint 7)) (.var 0))) (.base .u32) :=
  fun h => match h with
    | .fst hp => match hp with
      | .pair (_hl) hr => Dependent.erased_var_rejected rfl hr

example : ¬ H .execute one erased
    (.snd (.pair (.var 0) (.finite (.uint 7)))) (.base .u32) :=
  fun h => match h with
    | .snd hp => match hp with
      | .pair hl (_hr) => Dependent.erased_var_rejected rfl hl

example : H .ghost one erased (.pair (.var 0) (.refl (.var 0)))
    (.product (.base .u32) (.eq (.var 0) (.var 0))) :=
  .pair (.var .base True.intro True.intro) (.refl (.var rfl))

example : ¬ H .execute one runtime (.pair (.var 0) (.refl (.var 0)))
    (.product (.base .u32) (.eq (.var 0) (.var 0))) :=
  fun h => h.runtimeType.2

-- A constant condition still checks access in the unselected branch.
example : ¬ H .execute one erased
    (.cond (.boolean true) (.finite (.uint 7)) (.var 0)) (.base .u32) :=
  fun h => match h with
    | .cond (_hc) (_hq) (_ba) (_hl) hr => Dependent.erased_var_rejected rfl hr

example : ¬ H .execute one erased
    (.cond (.boolean false) (.var 0) (.finite (.uint 7))) (.base .u32) :=
  fun h => match h with
    | .cond (_hc) (_hq) (_ba) hl (_hr) => Dependent.erased_var_rejected rfl hl

example : ¬ H .ghost empty emptyQ
    (.cond (.boolean true) (.refl (.uint 7)) (.refl (.uint 7)))
    (.eq (.uint 7) (.uint 7)) :=
  fun h => match h with
    | .cond (_hc) (_hq) ha (_hl) (_hr) => ha

example : H .execute empty emptyQ
    (.inl (.base .bool) (.finite (.uint 7)))
    (.sum (.base .u32) (.base .bool)) :=
  .inl .base True.intro True.intro (.finite .uint True.intro)

example : H .execute empty emptyQ
    (.inr (.base .u32) (.finite (.boolean false)))
    (.sum (.base .u32) (.base .bool)) :=
  .inr .base True.intro True.intro (.finite .boolean True.intro)

example : ¬ H .ghost empty emptyQ
    (.inl (.base .bool) (.refl (.uint 7)))
    (.sum (.eq (.uint 7) (.uint 7)) (.base .bool)) :=
  fun h => match h with
    | .inl (_hb) ha (_bb) (_ht) => ha

-- Only the erased value changes to Ghost; the let body keeps Execute access.
example : H .execute one erased
    (.letIn .erase (.base .u32) (.finite (.var 0)) (.finite (.uint 7)))
    (.base .u32) :=
  .letIn .base .base (.finite (.var rfl) True.intro) (.finite .uint True.intro)

example : ¬ H .execute one erased
    (.letIn .run (.base .u32) (.finite (.var 0)) (.finite (.uint 7)))
    (.base .u32) :=
  fun h => match h with
    | .letIn (_ha) (_hb) hv (_hbody) => match hv with
      | .finite (_hi) hq => hq

example : ¬ H .execute one erased
    (.letIn .erase (.base .u32) (.finite (.var 0)) (.var 0)) (.base .u32) :=
  fun h => match h with
    | .letIn (_ha) (_hb) (_hv) hbody => Dependent.erased_var_rejected rfl hbody

example : ¬ H .execute one erased
    (.letIn .erase (.base .u32) (.finite (.var 0)) (.var 1)) (.base .u32) :=
  fun h => match h with
    | .letIn (_ha) (_hb) (_hv) hbody => Dependent.erased_var_rejected rfl hbody

example : H .execute one runtime
    (.letIn .erase (.eq (.var 0) (.var 0)) (.refl (.var 0)) (.var 1))
    (.base .u32) :=
  .letIn (.eq (.var rfl) (.var rfl)) .base (.refl (.var rfl))
    (.var .base True.intro True.intro)

def nestedLets : Dependent.Term 1 :=
  .letIn .erase (.eq (.var 0) (.var 0)) (.refl (.var 0))
    (.letIn .run (.base .bool) (.finite (.boolean true))
      (.ann (.var 1) (.eq (.var 2) (.var 2))))

theorem nestedLets_typed : H .ghost one erased nestedLets
    (.eq (.var 0) (.var 0)) :=
  .letIn (.eq (.var rfl) (.var rfl)) (.eq (.var rfl) (.var rfl))
    (.refl (.var rfl))
    (.letIn .base (.eq (.var rfl) (.var rfl)) (.finite .boolean True.intro)
      (.ann (.var (.eq (.var rfl) (.var rfl)) True.intro True.intro)))

example : Dependent.rename Fin.succ nestedLets =
    .letIn .erase (.eq (.var 1) (.var 1)) (.refl (.var 1))
      (.letIn .run (.base .bool) (.finite (.boolean true))
        (.ann (.var 1) (.eq (.var 3) (.var 3)))) := rfl

example : Dependent.rename id nestedLets = nestedLets :=
  Dependent.rename_id nestedLets

example : H .ghost (.snoc one (.base .bool)) (extendWith erased .run)
    (Dependent.rename Fin.succ nestedLets) (.eq (.var 1) (.var 1)) :=
  nestedLets_typed.weaken (.base .bool) .run

example : H .execute (.snoc evidence (.base .bool))
    (extendWith evidenceQ .erase)
    (Dependent.rename Fin.succ checkedPayload)
    (.refine .u32 (.var 0) (.uint 7)) :=
  checkedPayload_typed.rename Fin.succ (fun (_i) => rfl) (fun (_i) => rfl)

example : H .execute (.snoc empty (.base .bool)) (extendWith emptyQ .erase)
    (Dependent.rename Fin.succ dependentPair)
    (.sigma .u32 (.refine .u32 (.var 0) (.var 1))) :=
  dependentPair_typed.weaken (.base .bool) .erase

#print axioms Dependent.rename_identity
#print axioms Dependent.rename_id
#print axioms runtimeType_rename
#print axioms Dependent.HasType.wellFormed
#print axioms Dependent.HasType.runtimeType
#print axioms execute_equality_rejected
#print axioms Dependent.erased_var_rejected
#print axioms index_rename_instantiate
#print axioms schema_rename_instantiate
#print axioms quantityRenaming_access
#print axioms quantityRenaming_lift
#print axioms Dependent.HasType.rename
#print axioms Dependent.HasType.weaken

end DependentTermTest
