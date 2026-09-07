import AgentWasm

open AgentWasm.Finite

namespace BindingTest

-- Open replacements must skip each new binder, even with homogeneous types.
example : instantiate (.letIn .u32 (.var 0) (.add (.var 0) (.var 1)))
    (.var 0 : Term 1) = .letIn .u32 (.var 0) (.add (.var 0) (.var 1)) := rfl

example : instantiate
    (.letIn .u32 (.var 0) (.letIn .u32 (.var 1) (.var 2)))
    (.var 0 : Term 1) =
    .letIn .u32 (.var 0) (.letIn .u32 (.var 1) (.var 2)) := rfl

-- The removed binder differs from older variables, which decrement by one.
example : instantiate (.pair (.var 0) (.var 2)) (.boolean true : Term 2) =
    .pair (.boolean true) (.var 1) := rfl

-- Case binds each payload separately; its scrutinee stays outside both binders.
example : instantiate
    (.case .u32 (.var 0) (.add (.var 0) (.var 1)) (.var 1))
    (.var 0 : Term 1) =
    .case .u32 (.var 0) (.add (.var 0) (.var 1)) (.var 1) := rfl

example : rename (fun i : Fin 1 => i.succ)
    (.case .u32 (.var 0) (.var 0) (.var 1)) =
    (.case .u32 (.var 1) (.var 0) (.var 2) : Term 2) := rfl

example : instantiate (.letIn .bool (.var 0) (.var 0))
    (.boolean false : Term 0) = .letIn .bool (.boolean false) (.var 0) := rfl

-- Every non-binding constructor participates in substitution.
example : instantiate
    (.ann (.cond (.cmp .le (.var 0) (.uint 7))
      (.fst (.pair (.add (.var 0) (.uint 1)) (.boolean true)))
      (.snd (.pair (.boolean false) (.var 0)))) .u32)
    (.uint 4 : Term 0) =
    .ann (.cond (.cmp .le (.uint 4) (.uint 7))
      (.fst (.pair (.add (.uint 4) (.uint 1)) (.boolean true)))
      (.snd (.pair (.boolean false) (.uint 4)))) .u32 := rfl

example : instantiate (.pair (.inl .bool (.var 0)) (.inr .bool (.var 0)))
    (.uint 4294967295 : Term 0) =
    .pair (.inl .bool (.uint 4294967295)) (.inr .bool (.uint 4294967295)) := rfl

def empty : Context 0 := Fin.elim0
def outer : Context 1 := extend empty .u32

-- Heterogeneous binders make accidental use of the local payload ill typed.
def body : Term 2 :=
  .case .u32 (.inl .u32 (.var 0)) (.var 2) (.var 2)

theorem body_typed : HasType (extend outer .bool) body .u32 :=
  .case (.inl .var) .var .var

example : HasType outer (instantiate body (.boolean true)) .u32 :=
  body_typed.instantiate HasType.boolean

example : HasType (extend outer (.sum .u32 .bool))
    (rename Fin.succ (.var 0)) .u32 :=
  (HasType.var (Γ := outer) (i := 0)).weaken (.sum .u32 .bool)

-- Simultaneous substitution handles different source and destination scopes.
def source : Context 2 := extend outer .bool
def replacements : Substitution 2 0 :=
  Fin.cases (.boolean true) (Fin.cases (.uint 9) Fin.elim0)

theorem replacements_typed : SubstitutionPreserves source empty replacements :=
  Fin.cases HasType.boolean (Fin.cases HasType.uint (fun i => Fin.elim0 i))

example : HasType empty (subst replacements (.pair (.var 0) (.var 1)))
    (.product .bool .u32) :=
  (HasType.pair HasType.var HasType.var).subst replacements replacements_typed

-- Audit these declarations directly, including their transitive dependencies.
#print axioms HasType.rename
#print axioms HasType.weaken
#print axioms HasType.subst
#print axioms HasType.instantiate
#print axioms rename_id
#print axioms subst_id

end BindingTest
