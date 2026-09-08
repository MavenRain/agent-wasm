import AgentWasm.IndexedTypes

open AgentWasm
open AgentWasm.Finite

namespace IndexedTypeTest

abbrev I := Indexed.Ty
def empty : Context 0 := Fin.elim0
def one : Context 1 := extend empty .u32
def mixed : Context 2 := extend one .bool
def emptyQ : Phased.Quantities 0 := Fin.elim0
def runtime : Phased.Quantities 1 := Phased.extend emptyQ
def erased : Phased.Quantities 1 := Fin.cases .erase Fin.elim0

example : Indexed.instantiate (.eq (.var 0) (.add (.var 0) (.uint 1)))
    (.uint 7 : Term 0) = .eq (.uint 7) (.add (.uint 7) (.uint 1)) := rfl

example : Indexed.WellFormed empty (.eq (.uint 1) (.uint 2)) :=
  .eq .uint .uint

-- Formation checks endpoint types; it does not prove their equality.
example : ¬ Indexed.WellFormed empty (.eq (.boolean true) (.uint 1)) :=
  fun h => match h with
    | .eq hl (_hr) => nomatch hl

example : ¬ Indexed.WellFormed empty (.eq (.uint 1) (.boolean false)) :=
  fun h => match h with
    | .eq (_hl) hr => nomatch hr

def refinement : I 1 := .refine .u32 (.var 0) (.var 1)

theorem refinement_formed : Indexed.WellFormed one refinement :=
  .refine .var .var

example : Indexed.instantiate refinement (.uint 7 : Term 0) =
    .refine .u32 (.var 0) (.uint 7) := rfl

example : Indexed.WellFormed empty
    (Indexed.instantiate refinement (.uint 7)) :=
  refinement_formed.instantiate .uint

example : ¬ Indexed.WellFormed empty
    (.refine .bool (.boolean true) (.uint 1)) :=
  fun h => match h with
    | .refine hl (_hr) => nomatch hl

-- The bound boolean and payload stay local across two lifted substitutions.
def nested : I 1 :=
  .sigma .bool (.refine .u32 (.var 0) (.cond (.var 1) (.var 2) (.var 0)))

theorem nested_formed : Indexed.WellFormed one nested :=
  .sigma True.intro (.refine .var (.cond .var .var .var))

def openReplacement : Substitution 1 1 :=
  Fin.cases (.add (.var 0) (.uint 1)) Fin.elim0

theorem openReplacement_typed :
    SubstitutionPreserves one one openReplacement :=
  Fin.cases (.add .var .uint) (fun i => Fin.elim0 i)

example : Indexed.subst openReplacement nested =
    .sigma .bool (.refine .u32 (.var 0)
      (.cond (.var 1) (.add (.var 2) (.uint 1)) (.var 0))) := rfl

example : Indexed.WellFormed one (Indexed.subst openReplacement nested) :=
  nested_formed.subst openReplacement openReplacement_typed

example : Indexed.rename Fin.succ nested =
    .sigma .bool (.refine .u32 (.var 0)
      (.cond (.var 1) (.var 3) (.var 0))) := rfl

example : Indexed.WellFormed (extend one .bool)
    (Indexed.rename Fin.succ nested) := nested_formed.weaken .bool

def mixedRefinement : I 2 :=
  .refine .u32 (.cond (.var 1) (.var 0) (.var 2))
    (.add (.var 2) (.uint 1))

theorem mixedRefinement_formed : Indexed.WellFormed mixed mixedRefinement :=
  .refine (.cond .var .var .var) (.add .var .uint)

def mixedReplacement : Substitution 2 1 :=
  Fin.cases (.boolean true) (Fin.cases (.var 0) Fin.elim0)

theorem mixedReplacement_typed :
    SubstitutionPreserves mixed one mixedReplacement :=
  Fin.cases .boolean (Fin.cases .var (fun i => Fin.elim0 i))

example : Indexed.subst mixedReplacement mixedRefinement =
    .refine .u32 (.cond (.boolean true) (.var 0) (.var 1))
      (.add (.var 1) (.uint 1)) := rfl

example : Indexed.WellFormed one
    (Indexed.subst mixedReplacement mixedRefinement) :=
  mixedRefinement_formed.subst mixedReplacement mixedReplacement_typed

-- Types may keep an index that Execute cannot read from the target context.
theorem openReplacement_ghost :
    Phased.SubstitutionPreserves .ghost one runtime one erased openReplacement :=
  ⟨openReplacement_typed,
    fun i (_h) => Phased.allowed_ghost erased (openReplacement i)⟩

-- A Ghost typed replacement is accepted for a refinement schema too.
example : Indexed.WellFormed one
    (Indexed.subst openReplacement refinement) :=
  refinement_formed.subst_ghost openReplacement openReplacement_ghost

example : ¬ Phased.HasType .execute one erased
    (openReplacement 0) .u32 := fun h => h.2.1

-- Products can contain ghost evidence; branch results cannot contain it.
def evidenceProduct : I 0 :=
  .product (.base .bool) (.eq (.uint 0) (.uint 0))

example : Indexed.WellFormed empty evidenceProduct :=
  .product .base (.eq .uint .uint)

example : ¬ Indexed.BranchType evidenceProduct := fun h => h.2

example : ¬ Indexed.WellFormed empty
    (.sum (.eq (.uint 0) (.uint 0)) (.base .u32)) :=
  fun h => match h with
    | .sum ha (_hb) (_wa) (_wb) => ha

example : ¬ Indexed.WellFormed empty
    (.sum (.base .u32) evidenceProduct) :=
  fun h => match h with
    | .sum (_ha) hb (_wa) (_wb) => hb.2

example : ¬ Indexed.WellFormed empty
    (.sigma .u32 (.eq (.var 0) (.var 0))) :=
  fun h => match h with
    | .sigma hb (_wb) => hb

example : ¬ Indexed.WellFormed empty
    (.sigma .u32 (.product (.base .bool) (.eq (.var 0) (.var 0)))) :=
  fun h => match h with
    | .sigma hb (_wb) => hb.2

example : Indexed.WellFormed one
    (.sum refinement (.base (.sum .bool .u32))) :=
  .sum True.intro True.intro refinement_formed .base

example : Indexed.shape nested = some (.product .bool .u32) := rfl
example : Indexed.shape evidenceProduct = none := rfl
example : Indexed.shape (Indexed.subst openReplacement nested) =
    some (.product .bool .u32) := Indexed.shape_subst nested openReplacement
example : Indexed.shape (Indexed.rename Fin.succ nested) =
    some (.product .bool .u32) := Indexed.shape_rename nested Fin.succ

example : Indexed.rename Fin.succ (Indexed.rename Fin.succ nested) =
    Indexed.rename (fun i => i.succ.succ) nested :=
  Indexed.rename_comp nested Fin.succ Fin.succ

example : Indexed.subst (liftSub mixedReplacement)
    (Indexed.rename Fin.succ mixedRefinement) =
    Indexed.subst (fun i => liftSub mixedReplacement i.succ) mixedRefinement :=
  Indexed.subst_rename mixedRefinement Fin.succ (liftSub mixedReplacement)

example : Indexed.rename Fin.succ (Indexed.subst openReplacement nested) =
    Indexed.subst (fun i => rename Fin.succ (openReplacement i)) nested :=
  Indexed.rename_subst nested openReplacement Fin.succ

example : Indexed.subst openReplacement
    (Indexed.subst mixedReplacement mixedRefinement) =
    Indexed.subst (fun i => subst openReplacement (mixedReplacement i))
      mixedRefinement :=
  Indexed.subst_comp mixedRefinement mixedReplacement openReplacement

example : Indexed.instantiate (Indexed.rename Fin.succ nested)
    (.add (.var 0) (.uint 2)) = nested :=
  Indexed.instantiate_weaken nested (.add (.var 0) (.uint 2))

def outerFamily : I 2 :=
  .sigma .bool (.refine .u32 (.var 0) (.add (.var 2) (.var 3)))

example : Indexed.instantiate outerFamily (.var 0) =
    .sigma .bool (.refine .u32 (.var 0) (.add (.var 2) (.var 2))) := rfl

example : Indexed.subst openReplacement
    (Indexed.instantiate outerFamily (.var 0)) =
    Indexed.instantiate (Indexed.subst (liftSub openReplacement) outerFamily)
      (subst openReplacement (.var 0)) :=
  Indexed.subst_instantiate outerFamily (.var 0) openReplacement

#print axioms Indexed.rename_id
#print axioms Indexed.subst_id
#print axioms Indexed.branch_rename
#print axioms Indexed.branch_subst
#print axioms Indexed.WellFormed.rename
#print axioms Indexed.WellFormed.weaken
#print axioms Indexed.WellFormed.subst
#print axioms Indexed.WellFormed.instantiate
#print axioms Indexed.WellFormed.subst_ghost
#print axioms Indexed.shape_rename
#print axioms Indexed.shape_subst
#print axioms Indexed.rename_comp
#print axioms Indexed.subst_rename
#print axioms Indexed.rename_subst
#print axioms Indexed.subst_comp
#print axioms Indexed.instantiate_weaken
#print axioms Indexed.subst_instantiate
#print axioms Indexed.rename_identity
#print axioms Indexed.subst_identity
#print axioms Indexed.rename_composition
#print axioms Indexed.subst_renaming
#print axioms Indexed.rename_substitution
#print axioms Indexed.subst_composition

end IndexedTypeTest
