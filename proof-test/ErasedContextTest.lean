import AgentWasm.ErasedContexts

open AgentWasm.Finite

namespace ErasedContextTest

abbrev P {n : Nat} := @Phased.HasType n
def empty : Context 0 := Fin.elim0
def emptyQ : Phased.Quantities 0 := Fin.elim0
def one : Context 1 := extend empty .u32
def erased : Phased.Quantities 1 := Phased.extendWith emptyQ .erase
def runtime : Phased.Quantities 1 := Phased.extendWith emptyQ .run

example : Phased.extendWith runtime .run = Phased.extend runtime := rfl

example : ¬ P .execute (extend one .bool)
    (Phased.extendWith runtime .erase) (.var 0) .bool :=
  Phased.erased_var_rejected rfl

example : P .execute (extend one .bool)
    (Phased.extendWith runtime .erase) (rename Fin.succ (.var 0)) .u32 :=
  (show P .execute one runtime (.var 0) .u32 from
    ⟨.var, True.intro⟩).weakenWith .bool .erase

example : P .execute (extend one .bool)
    (Phased.extendWith runtime .run) (rename Fin.succ (.var 0)) .u32 :=
  (show P .execute one runtime (.var 0) .u32 from
    ⟨.var, True.intro⟩).weakenWith .bool .run

example : P .ghost (extend one .bool)
    (Phased.extendWith erased .erase) (rename Fin.succ (.var 0)) .u32 :=
  (Phased.HasType.ghost (q := erased)
    (HasType.var (Γ := one) (i := 0))).weakenWith .bool .erase

-- An open replacement can remain inaccessible in Execute.
theorem replacement_ghost : P .ghost one erased (.var 0) .u32 :=
  Phased.HasType.ghost .var

example : ¬ P .execute one erased (.var 0) .u32 :=
  Phased.erased_var_rejected rfl

def executeBody : Term 2 :=
  .letIn .u32 (.uint 3)
    (.case .u32 (.inl .bool (.var 0))
      (.add (.var 0) (.var 1)) (.var 1))

theorem executeBody_typed : P .execute (extend one .u32)
    (Phased.extendWith erased .erase) executeBody .u32 :=
  ⟨.letIn .uint (.case (.inl .var) (.add .var .var) .var),
    ⟨True.intro, True.intro, ⟨True.intro, True.intro⟩, True.intro⟩⟩

example : P .execute one erased (instantiate executeBody (.var 0)) .u32 :=
  executeBody_typed.instantiate_erased replacement_ghost

-- Runtime binders keep the open replacement clear of local variables.
def ghostBody : Term 2 :=
  .letIn .bool (.boolean true)
    (.case .u32 (.inl .bool (.var 1))
      (.add (.var 0) (.var 2)) (.var 2))

theorem ghostBody_typed : P .ghost (extend one .u32)
    (Phased.extendWith erased .erase) ghostBody .u32 :=
  Phased.HasType.ghost
    (.letIn .boolean (.case (.inl .var) (.add .var .var) .var))

example : P .ghost one erased (instantiate ghostBody (.var 0)) .u32 :=
  ghostBody_typed.instantiate_erased replacement_ghost

example : instantiate ghostBody (.var 0) =
    .letIn .bool (.boolean true)
      (.case .u32 (.inl .bool (.var 1))
        (.add (.var 0) (.var 2)) (.var 2)) := rfl

-- The erased slot is still forbidden beneath runtime let and case binders.
example : ¬ P .execute (extend one .u32)
    (Phased.extendWith runtime .erase) ghostBody .u32 :=
  fun h => h.2.2.1

example : ¬ P .execute (extend one .u32)
    (Phased.extendWith runtime .erase)
    (.case .u32 (.inl .bool (.uint 1)) (.var 1) (.uint 0)) .u32 :=
  fun h => h.2.2.1

example : ¬ P .execute (extend one .u32)
    (Phased.extendWith runtime .erase)
    (.case .u32 (.inr .u32 (.boolean true)) (.uint 0) (.var 1)) .u32 :=
  fun h => h.2.2.2

#print axioms Phased.Allowed.weakenWith
#print axioms Phased.HasType.weakenWith
#print axioms Phased.Allowed.instantiate_erased
#print axioms Phased.HasType.instantiate_erased

end ErasedContextTest
