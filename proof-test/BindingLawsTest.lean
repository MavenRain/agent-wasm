import AgentWasm.BindingLaws

open AgentWasm.Finite

namespace BindingLawsTest

-- Both branches contain open variables beside payload and let binders.
def openBranches : Term 2 :=
  .case .u32 (.inl .u32 (.var 0))
    (.letIn .u32 (.add (.var 0) (.var 1))
      (.letIn .u32 (.var 2) (.add (.var 1) (.var 4))))
    (.letIn .u32 (.var 2) (.add (.var 1) (.var 2)))

def first : Substitution 2 2 :=
  Fin.cases (.add (.var 1) (.uint 3)) (Fin.cases (.var 0) Fin.elim0)

def second : Substitution 2 1 :=
  Fin.cases (.add (.var 0) (.uint 7)) (Fin.cases (.var 0) Fin.elim0)

-- The surviving outer variable passes three binders in the nested left branch.
def expected : Term 1 :=
  .case .u32 (.inl .u32 (.add (.var 0) (.uint 3)))
    (.letIn .u32 (.add (.var 0) (.add (.var 1) (.uint 3)))
      (.letIn .u32 (.add (.var 2) (.uint 3))
        (.add (.var 1) (.add (.var 3) (.uint 7)))))
    (.letIn .u32 (.add (.var 1) (.uint 7))
      (.add (.var 1) (.add (.var 2) (.uint 3))))

example : subst second (subst first openBranches) = expected := rfl

example : subst (fun i => subst second (first i)) openBranches = expected := rfl

example : subst second (subst first openBranches) =
    subst (fun i => subst second (first i)) openBranches :=
  subst_comp openBranches first second

example : rename Fin.succ (subst first openBranches) =
    subst (fun i => rename Fin.succ (first i)) openBranches :=
  rename_subst openBranches first Fin.succ

example : subst (liftSub first) (rename Fin.succ openBranches) =
    rename Fin.succ (subst first openBranches) :=
  subst_weaken openBranches first

example : rename (liftRen Fin.succ) (rename Fin.succ openBranches) =
    rename Fin.succ (rename Fin.succ openBranches) :=
  rename_weaken openBranches Fin.succ

-- Removing a binder after weakening must preserve every open reference.
example : instantiate (rename Fin.succ openBranches) (.var 1) = openBranches :=
  instantiate_weaken openBranches (.var 1)

-- Instantiation and a later open substitution act on both branch bodies.
example : subst second (instantiate (rename Fin.succ openBranches) (.var 1)) =
    instantiate (subst (liftSub second) (rename Fin.succ openBranches))
      (subst second (.var 1)) :=
  subst_instantiate (rename Fin.succ openBranches) (.var 1) second

-- Pointwise equal maps give equal results through every binder.
example : rename Fin.succ openBranches =
    rename (fun i => i.succ) openBranches :=
  rename_congr openBranches Fin.succ (fun i => i.succ) (fun (_i) => rfl)

example : subst first openBranches = subst (fun i => first i) openBranches :=
  subst_congr openBranches first (fun i => first i) (fun (_i) => rfl)

-- Directly check a used binder, plus an older variable under the right branch.
def later : Substitution 1 1 := fun (_i) => .add (.var 0) (.uint 5)

example : subst later
    (instantiate openBranches (.add (.var 0) (.uint 9))) =
    instantiate
      (subst (liftSub later) openBranches)
      (.add (.add (.var 0) (.uint 5)) (.uint 9)) :=
  subst_instantiate openBranches (.add (.var 0) (.uint 9))
    later

-- Audit the generalized pointwise laws and all public corollaries.
#print axioms rename_composition
#print axioms rename_comp
#print axioms rename_congr
#print axioms rename_weaken
#print axioms subst_renaming
#print axioms subst_rename
#print axioms subst_congr
#print axioms rename_substitution
#print axioms rename_subst
#print axioms subst_weaken
#print axioms subst_composition
#print axioms subst_comp
#print axioms instantiate_weaken
#print axioms subst_instantiate

end BindingLawsTest
