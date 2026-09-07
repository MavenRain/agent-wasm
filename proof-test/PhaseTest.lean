import AgentWasm

open AgentWasm.Finite

namespace PhaseTest

abbrev P {n : Nat} := @Phased.HasType n
def empty : Context 0 := Fin.elim0
def emptyQ : Phased.Quantities 0 := Fin.elim0
def one : Context 1 := extend empty .u32
def erased : Phased.Quantities 1 := Fin.cases .erase Fin.elim0
def runtime : Phased.Quantities 1 := Phased.extend emptyQ

example : P .execute one runtime (.var 0) .u32 := ⟨.var, True.intro⟩
example : P .ghost one erased (.var 0) .u32 := Phased.HasType.ghost .var
example : ¬ P .execute one erased (.var 0) .u32 :=
  Phased.erased_var_rejected rfl

-- Even an unselected branch must obey the enclosing phase.
example : ¬ P .execute one erased
    (.cond (.boolean true) (.uint 1) (.var 0)) .u32 :=
  fun h => h.2.2.2

-- Both eager pair components, comparisons, and annotations enforce access.
example : ¬ P .execute one erased
    (.ann (.fst (.pair (.uint 1) (.add (.uint 2) (.var 0)))) .u32) .u32 :=
  fun h => h.2.2.2
example : ¬ P .execute one erased (.fst (.pair (.var 0) (.uint 1))) .u32 :=
  fun h => h.2.1
example : ¬ P .execute one erased (.cmp .le (.var 0) (.uint 1)) .bool :=
  fun h => h.2.1

def body : Term 2 :=
  .letIn .bool (.boolean true)
    (.case .u32 (.inl .bool (.var 1)) (.var 0) (.var 2))

theorem body_typed : P .execute (extend one .u32)
    (Phased.extend erased) body .u32 :=
  ⟨.letIn .boolean (.case (.inl .var) .var .var),
    ⟨True.intro, True.intro, True.intro, True.intro⟩⟩

-- The replacement is open, and each new runtime binder shifts its access map.
example : P .execute one runtime (instantiate body (.var 0)) .u32 :=
  (show P .execute (extend one .u32) (Phased.extend runtime) body .u32 from
    ⟨body_typed.1, ⟨True.intro, True.intro, True.intro, True.intro⟩⟩).instantiate
      ⟨.var, True.intro⟩

example : P .execute one erased (instantiate body (.uint 7)) .u32 :=
  body_typed.instantiate ⟨.uint, True.intro⟩

-- Outer erased variables stay inaccessible below runtime binders.
example : ¬ P .execute one erased
    (.letIn .bool (.boolean true) (.var 1)) .u32 := fun h => h.2.2
example : ¬ P .execute one erased
    (.case .u32 (.inl .bool (.uint 1)) (.var 1) (.uint 0)) .u32 :=
  fun h => h.2.2.1
example : ¬ P .execute one erased
    (.case .u32 (.inr .u32 (.boolean true)) (.uint 0) (.var 1)) .u32 :=
  fun h => h.2.2.2

-- Same types alone cannot authorize a runtime-to-erased variable map.
example : ¬ Phased.RenamingPreserves .execute runtime erased id :=
  fun h => h 0 True.intro
example : ¬ Phased.SubstitutionPreserves .execute one runtime one erased
    Term.var := fun h => h.2 0 True.intro

theorem ghost_replacements :
    Phased.SubstitutionPreserves .ghost one runtime one erased Term.var :=
  ⟨fun (_i) => .var, fun i (_h) => Phased.allowed_ghost erased (.var i)⟩

example : P .ghost one erased (subst Term.var (.var 0)) .u32 :=
  (Phased.HasType.ghost (q := runtime) (HasType.var (Γ := one) (i := 0))).subst
    Term.var ghost_replacements

-- An inaccessible source slot can keep an inaccessible, well-typed replacement.
theorem erased_replacements :
    Phased.SubstitutionPreserves .execute one erased one erased Term.var :=
  ⟨fun (_i) => .var, fun (_i) h => h⟩

example : P .execute one erased (subst Term.var (.uint 9)) .u32 :=
  (show P .execute one erased (.uint 9) .u32 from ⟨.uint, True.intro⟩).subst
    Term.var erased_replacements

example : P .execute (extend one .bool) (Phased.extend runtime)
    (rename Fin.succ (.var 0)) .u32 :=
  (show P .execute one runtime (.var 0) .u32 from ⟨.var, True.intro⟩).weaken .bool

#print axioms Phased.HasType.rename
#print axioms Phased.HasType.weaken
#print axioms Phased.HasType.subst
#print axioms Phased.HasType.instantiate
#print axioms Phased.HasType.ghost
#print axioms Phased.erased_var_rejected

end PhaseTest
