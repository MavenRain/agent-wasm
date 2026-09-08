import AgentWasm.DependentTerms

open AgentWasm
open AgentWasm.Finite.Phased
open AgentWasm.Dependent

namespace DependentBranchTest

abbrev H {n : Nat} := @Dependent.HasType n

def empty : Dependent.Context 0 := .nil
def emptyQ : Quantities 0 := Fin.elim0
def scalar : Dependent.Context 1 := .snoc empty (.base .u32)
def boolean : Dependent.Context 1 := .snoc empty (.base .bool)
def runtime : Quantities 1 := extendWith emptyQ .run
def erased : Quantities 1 := extendWith emptyQ .erase

-- The left payload retains a schema that refers to the outer scalar.
def refined : Indexed.Ty 1 := .refine .u32 (.var 0) (.var 1)

def refinedSum : Dependent.Term 1 :=
  .inl (.base .bool)
    (.pack .u32 (.var 0) (.var 1) (.var 0) (.refl (.var 0)))

theorem refinedSum_typed : H .execute scalar runtime refinedSum
    (.sum refined (.base .bool)) :=
  .inl .base True.intro True.intro
    (.pack (.refine (.var rfl) (.var rfl)) (.var rfl) True.intro
      (.refl (.var rfl)))

def refinedCase : Dependent.Term 1 :=
  .case refined refinedSum (.var 0)
    (.pack .u32 (.var 0) (.var 2) (.var 1) (.refl (.var 1)))

theorem refinedCase_typed : H .execute scalar runtime refinedCase refined :=
  .case (.refine (.var rfl) (.var rfl)) True.intro refinedSum_typed
    (.var (.refine (.var rfl) (.var rfl)) True.intro True.intro)
    (.pack (.refine (.var rfl) (.var rfl)) (.var rfl) True.intro
      (.refl (.var rfl)))

example : H .execute scalar runtime (.value refinedCase) (.base .u32) :=
  .value refinedCase_typed

example : Dependent.rename Fin.succ refinedCase =
    .case (.refine .u32 (.var 0) (.var 2))
      (.inl (.base .bool)
        (.pack .u32 (.var 0) (.var 2) (.var 1) (.refl (.var 1))))
      (.var 0)
      (.pack .u32 (.var 0) (.var 3) (.var 2) (.refl (.var 2))) := rfl

example : H .execute (.snoc scalar (branchEvidence (.boolean true) 1))
    (extendWith runtime .erase) (Dependent.rename Fin.succ refinedCase)
    (.refine .u32 (.var 0) (.var 2)) :=
  refinedCase_typed.weaken (branchEvidence (.boolean true) 1) .erase

example : Dependent.rename id refinedCase = refinedCase :=
  Dependent.rename_id refinedCase

-- Both handlers have runtime payload binders.
example : H .execute empty emptyQ
    (.case (.base .u32)
      (.inr (.base .u32) (.finite (.uint 7))) (.var 0) (.var 0))
    (.base .u32) :=
  .case .base True.intro
    (.inr (b := .base .u32) .base True.intro True.intro
      (.finite .uint True.intro))
    (.var .base True.intro True.intro) (.var .base True.intro True.intro)

-- Distinct payload types ensure the right arm uses the right declaration.
example : H .execute empty emptyQ
    (.case (.base .bool)
      (.inr (.base .u32) (.finite (.boolean true)))
      (.finite (.boolean false)) (.var 0)) (.base .bool) :=
  .case .base True.intro
    (.inr (b := .base .bool) .base True.intro True.intro
      (.finite .boolean True.intro))
    (.finite .boolean True.intro) (.var .base True.intro True.intro)

example : ¬ H .execute empty emptyQ
    (.case (.base .u32)
      (.inr (.base .u32) (.finite (.boolean true))) (.var 0) (.var 0))
    (.base .u32) :=
  fun h => match h with
    | .case (_ha) (_ba) hs (_hl) hr => match hs with
      | .inr (_wa) (_ba) (_bb) hv => match hv with
        | .finite hi (_hq) => match hi with | .boolean => nomatch hr

-- Neither branch selection nor a new payload permits erased outer access.
example : ¬ H .execute scalar erased
    (.case (.base .u32)
      (.inl (.base .u32) (.finite (.uint 7))) (.var 0) (.var 1))
    (.base .u32) :=
  fun h => match h with
    | .case (_ha) (_ba) (_hs) (_hl) hr =>
        Dependent.erased_var_rejected rfl hr

example : ¬ H .execute scalar erased
    (.case (.base .u32)
      (.inr (.base .u32) (.finite (.uint 7))) (.var 1) (.var 0))
    (.base .u32) :=
  fun h => match h with
    | .case (_ha) (_ba) (_hs) hl (_hr) =>
        Dependent.erased_var_rejected rfl hl

example : ¬ H .ghost empty emptyQ
    (.case (.eq (.uint 7) (.uint 7))
      (.inl (.base .u32) (.finite (.uint 7)))
      (.refl (.uint 7)) (.refl (.uint 7))) (.eq (.uint 7) (.uint 7)) :=
  fun h => match h with
    | .case (_ha) ba (_hs) (_hl) (_hr) => ba

-- The explicit outer result cannot be replaced by a payload-dependent type.
example : ¬ H .execute scalar runtime
    (.case refined
      (.inl (.base .u32) (.finite (.uint 7)))
      (.pack .u32 (.var 0) (.var 1) (.var 0) (.refl (.var 0)))
      (.pack .u32 (.var 0) (.var 2) (.var 1) (.refl (.var 1)))) refined :=
  fun h => match h with
    | .case (_ha) (_ba) (_hs) hl (_hr) => nomatch hl

-- Each checked branch consumes its own erased evidence inside a package.
def decision : Indexed.Ty 1 :=
  .refine .u32 (.cond (.var 1) (.uint 1) (.uint 0)) (.var 0)

def decisionArm (outcome : Fin (2 ^ 32)) : Dependent.Term 2 :=
  .pack .u32 (.cond (.var 2) (.uint 1) (.uint 0))
    (.var 0) (.uint outcome) (.var 0)

def checkedDecision : Dependent.Term 1 :=
  .ifProof decision (.var 0) (decisionArm 1) (decisionArm 0)

theorem checkedDecision_typed :
    H .execute boolean runtime checkedDecision decision :=
  .ifProof (.refine (.cond (.var rfl) .uint .uint) (.var rfl))
    True.intro (.var rfl) True.intro
    (.pack (.refine (.cond (.var rfl) .uint .uint) (.var rfl))
      .uint True.intro
      (.var (.eq (.cond (.var rfl) .uint .uint) .uint)
        True.intro True.intro))
    (.pack (.refine (.cond (.var rfl) .uint .uint) (.var rfl))
      .uint True.intro
      (.var (.eq (.cond (.var rfl) .uint .uint) .uint)
        True.intro True.intro))

example : H .execute boolean runtime (.value checkedDecision) (.base .u32) :=
  .value checkedDecision_typed

example : Dependent.rename Fin.succ checkedDecision =
    .ifProof (.refine .u32 (indicator (.var 2)) (.var 0)) (.var 1)
      (.pack .u32 (indicator (.var 3)) (.var 0) (.uint 1) (.var 0))
      (.pack .u32 (indicator (.var 3)) (.var 0) (.uint 0) (.var 0)) := rfl

example : Dependent.rename id checkedDecision = checkedDecision :=
  Dependent.rename_id checkedDecision

example : H .execute (.snoc boolean (.base .u32))
    (extendWith runtime .erase) (Dependent.rename Fin.succ checkedDecision)
    (.refine .u32 (indicator (.var 2)) (.var 0)) :=
  checkedDecision_typed.weaken (.base .u32) .erase

-- Wrong outcomes and swapped evidence cannot satisfy exact schema equality.
example : ¬ H .execute boolean runtime
    (.ifProof decision (.var 0) (decisionArm 1) (decisionArm 1)) decision :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) (_hq) (_hl) hr =>
        match hr with | .pack (_wf) (_hv) (_hqv) hp => nomatch hp

example : ¬ H .execute boolean runtime
    (.ifProof decision (.var 0) (decisionArm 0) (decisionArm 0)) decision :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) (_hq) hl (_hr) =>
        match hl with | .pack (_wf) (_hv) (_hqv) hp => nomatch hp

-- Checking the condition remains in the enclosing phase.
example : ¬ H .execute boolean erased checkedDecision decision :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) hq (_hl) (_hr) => hq

example : H .ghost boolean erased
    (.ifProof (.base .u32) (.var 0)
      (.finite (.uint 1)) (.finite (.uint 0))) (.base .u32) :=
  .ifProof .base True.intro (.var rfl) True.intro
    (.finite .uint True.intro) (.finite .uint True.intro)

example : ¬ H .ghost empty emptyQ
    (.ifProof (.base .u32) (.uint 1)
      (.finite (.uint 1)) (.finite (.uint 0))) (.base .u32) :=
  fun h => match h with
    | .ifProof (_ha) (_ba) hc (_hq) (_hl) (_hr) => nomatch hc

-- A proof variable cannot be evaluated even when its value is discarded.
example : ¬ H .execute boolean runtime
    (.ifProof (.base .u32) (.var 0)
      (.finite (.uint 1)) (.fst (.pair (.finite (.uint 0)) (.var 0))))
    (.base .u32) :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) (_hq) (_hl) hr => match hr with
      | .fst hp => match hp with
        | .pair (_hv) he => Dependent.erased_var_rejected rfl he

example : ¬ H .execute boolean runtime
    (.ifProof (.base .u32) (.var 0)
      (.fst (.pair (.finite (.uint 1)) (.var 0))) (.finite (.uint 0)))
    (.base .u32) :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) (_hq) hl (_hr) => match hl with
      | .fst hp => match hp with
        | .pair (_hv) he => Dependent.erased_var_rejected rfl he

example : ¬ H .ghost empty emptyQ
    (.ifProof (branchEvidence (.boolean true) 1) (.boolean true)
      (.var 0) (.var 0)) (branchEvidence (.boolean true) 1) :=
  fun h => match h with
    | .ifProof (_ha) ba (_hc) (_hq) (_hl) (_hr) => ba

#print axioms indicator_rename
#print axioms branchEvidence_rename
#print axioms indicator_hasType
#print axioms branchEvidence_wellFormed

end DependentBranchTest
