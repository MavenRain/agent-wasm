import AgentWasm.DependentTerms

open AgentWasm
open AgentWasm.Finite
open AgentWasm.Finite.Phased
open AgentWasm.Dependent

namespace DependentIndexTest

abbrev H {n : Nat} := @Dependent.HasType n

def empty : Dependent.Context 0 := .nil
def scalar : Dependent.Context 1 := .snoc empty (.base .u32)
def refined : Dependent.Context 2 :=
  .snoc scalar (.refine .u32 (.var 0) (.var 1))
def telescope : Dependent.Context 3 :=
  .snoc refined (.sigma .bool
    (.refine .u32 (.var 0) (.value (.var 2))))

theorem telescope_formed : Dependent.Context.WellFormed telescope :=
  .snoc (.snoc (.snoc .nil .base) (.refine (.var rfl) (.var rfl)))
    (.sigma True.intro (.refine (.var rfl) (.value (.var True.intro))))

-- The declaration's own binder and newer entries both shift outer endpoints.
example : lookup telescope 1 = .refine .u32 (.var 0) (.var 3) := rfl
example : lookup telescope 0 =
    .sigma .bool (.refine .u32 (.var 0) (.value (.var 3))) := rfl

example : lookup telescope 1 ≠ .refine .u32 (.var 0) (.var 2) :=
  fun h => (show (3 : Nat) ≠ 2 from of_decide_eq_true rfl)
    (congrArg Fin.val (Finite.Term.var.inj (Indexed.Ty.refine.inj h).2.2))

def computedProduct : Finite.Term 3 :=
  .cond (.boolean true) (.pair (.var 1) (.var 0))
    (.pair (.var 1) (.var 0))

theorem computedProduct_schema : IndexHasSchema telescope computedProduct
    (.product (.refine .u32 (.var 0) (.var 3))
      (.sigma .bool (.refine .u32 (.var 0) (.value (.var 3))))) :=
  .cond .boolean ⟨True.intro, True.intro⟩
    (.pair (.var True.intro) (.var True.intro))
    (.pair (.var True.intro) (.var True.intro))

example : Dependent.WellFormed telescope
    (.product (.refine .u32 (.var 0) (.var 3))
      (.sigma .bool (.refine .u32 (.var 0) (.value (.var 3))))) :=
  computedProduct_schema.wellFormed telescope_formed

example : Indexed.BranchType
    (.product (.refine .u32 (.var 0) (.var 3))
      (.sigma .bool (.refine .u32 (.var 0) (.value (.var 3)))) : Indexed.Ty 3) :=
  computedProduct_schema.branchType

theorem computedValue_typed :
    IndexHasType telescope (.value (.fst computedProduct)) .u32 :=
  .value (.fst computedProduct_schema)

theorem computedFirst_typed :
    IndexHasType telescope (.dfst (.snd computedProduct)) .bool :=
  .dfst (.snd computedProduct_schema)

example : IndexHasSchema (.snoc telescope (.base .u32))
    (Finite.rename Fin.succ computedProduct)
    (.product (.refine .u32 (.var 0) (.var 4))
      (.sigma .bool (.refine .u32 (.var 0) (.value (.var 4))))) :=
  computedProduct_schema.weaken (.base .u32)

-- The finite result is available only after its explicit dependent projection.
example : Indexed.shape (lookup telescope 1) = some .u32 := rfl
example : ¬ IndexHasType telescope (.var 1) .u32 :=
  fun h => match h with | .var hl => nomatch hl

example : ¬ IndexHasType telescope (.fst (.var 0)) .bool :=
  fun h => match h with | .fst (.var hl) => nomatch hl

example : ¬ IndexHasType telescope (.value (.var 0)) .u32 :=
  fun h => match h with | .value hs => nomatch hs

example : ¬ IndexHasType telescope (.dfst (.var 1)) .u32 :=
  fun h => match h with | .dfst hs => nomatch hs

example : ¬ IndexHasType telescope (.value (.uint 7)) .u32 :=
  fun h => match h with | .value hs => nomatch hs

example : ¬ IndexHasSchema telescope (.var 1)
    (.refine .u32 (.var 0) (.var 2)) := fun h => nomatch h

-- Equal representation shapes do not make distinct refinement schemas equal.
def distinct : Dependent.Context 2 :=
  .snoc (.snoc empty (.refine .u32 (.var 0) (.uint 7)))
    (.refine .u32 (.var 0) (.uint 8))

example : ¬ IndexHasSchema distinct
    (.cond (.boolean true) (.var 0) (.var 1))
    (.refine .u32 (.var 0) (.uint 8)) :=
  fun h => match h with | .cond (_hc) (_ba) (_hl) hr => nomatch hr

-- A computed schema requires a Boolean condition, not a u32 literal.
example : ¬ IndexHasSchema refined
    (.cond (.uint 3) (.var 0) (.var 0)) (lookup refined 0) :=
  fun h => match h with | .cond hc (_ba) (_hl) (_hr) => nomatch hc

def equality : Dependent.Context 1 := .snoc empty (.eq (.uint 7) (.uint 7))

example : ¬ IndexHasSchema equality (.var 0) (.eq (.uint 7) (.uint 7)) :=
  fun h => h.branchType

example : ¬ IndexHasSchema equality
    (.cond (.boolean true) (.var 0) (.var 0)) (.eq (.uint 7) (.uint 7)) :=
  fun h => h.branchType

-- Projections participate in endpoints, including beneath new schema binders.
example : Dependent.WellFormed telescope
    (.eq (.value (.fst computedProduct)) (.uint 7)) :=
  .eq computedValue_typed .uint

example : Dependent.WellFormed telescope
    (.sigma .bool (.refine .u32 (.var 0)
      (.cond (.dfst (.var 2)) (.value (.var 3)) (.var 0)))) :=
  .sigma True.intro
    (.refine (.var rfl)
      (.cond (.dfst (.var True.intro)) (.value (.var True.intro)) (.var rfl)))

def boundIndex : Finite.Term 3 :=
  .letIn .u32 (.value (.var 1))
    (.case .u32 (.inl .bool (.var 0))
      (.add (.var 0) (.value (.var 3)))
      (.cond (.dfst (.var 2)) (.var 1) (.value (.var 3))))

theorem boundIndex_typed : IndexHasType telescope boundIndex .u32 :=
  .letIn (.value (.var True.intro))
    (.case (.inl (.var rfl)) (.add (.var rfl) (.value (.var True.intro)))
      (.cond (.dfst (.var True.intro)) (.var rfl) (.value (.var True.intro))))

example : Finite.rename Fin.succ boundIndex =
    .letIn .u32 (.value (.var 2))
      (.case .u32 (.inl .bool (.var 0))
        (.add (.var 0) (.value (.var 4)))
        (.cond (.dfst (.var 3)) (.var 1) (.value (.var 4)))) := rfl

example : IndexHasType (.snoc telescope (.base .bool))
    (Finite.rename Fin.succ boundIndex) .u32 :=
  boundIndex_typed.weaken (.base .bool)

def emptyQ : Quantities 0 := Fin.elim0
def runtime : Quantities 3 :=
  extendWith (extendWith (extendWith emptyQ .run) .run) .run

example : H .execute telescope runtime
    (.ifProof (.base .u32) (.dfst (.snd computedProduct))
      (.finite (.value (.var 2))) (.finite (.uint 0))) (.base .u32) :=
  .ifProof .base True.intro computedFirst_typed
    ⟨True.intro, ⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩
    (.finite (.value (.var True.intro)) True.intro) (.finite .uint True.intro)

example : Dependent.WellFormed telescope
    (branchEvidence (.dfst (.snd computedProduct)) 1) :=
  branchEvidence_wellFormed computedFirst_typed 1

def sameRefinements : Dependent.Context 2 :=
  .snoc (.snoc empty (.refine .u32 (.var 0) (.uint 7)))
    (.refine .u32 (.var 0) (.uint 7))
def mixedQ : Quantities 2 := extendWith (extendWith emptyQ .run) .erase

example : ¬ H .execute sameRefinements mixedQ
    (.finite (.value (.var 0))) (.base .u32) :=
  fun h => match h with | .finite (_ht) hq => hq

example : H .ghost sameRefinements mixedQ
    (.finite (.value (.var 0))) (.base .u32) :=
  .finite (.value (.var True.intro)) True.intro

-- A discarded conditional operand still requires access to its entire input.
example : ¬ H .execute sameRefinements mixedQ
    (.finite (.value (.cond (.boolean true) (.var 1) (.var 0))))
    (.base .u32) :=
  fun h => match h with | .finite (_ht) hq => hq.2.2

example : ¬ H .execute sameRefinements mixedQ
    (.finite (.value (.cond (.boolean false) (.var 0) (.var 1))))
    (.base .u32) :=
  fun h => match h with | .finite (_ht) hq => hq.2.1

example : H .ghost sameRefinements mixedQ
    (.finite (.value (.cond (.boolean true) (.var 1) (.var 0))))
    (.base .u32) :=
  .finite (.value (.cond (a := .refine .u32 (.var 0) (.uint 7))
    .boolean True.intro (.var True.intro) (.var True.intro)))
    (allowed_ghost mixedQ _)

def sameSigmas : Dependent.Context 2 :=
  .snoc (.snoc empty (.sigma .bool (.base .u32)))
    (.sigma .bool (.base .u32))

example : ¬ H .execute sameSigmas mixedQ
    (.finite (.dfst (.cond (.boolean true) (.var 1) (.var 0))))
    (.base .bool) :=
  fun h => match h with | .finite (_ht) hq => hq.2.2

example : H .ghost sameSigmas mixedQ
    (.finite (.dfst (.cond (.boolean true) (.var 1) (.var 0))))
    (.base .bool) :=
  .finite (.dfst (.cond (a := .sigma .bool (.base .u32))
    .boolean True.intro (.var True.intro) (.var True.intro)))
    (allowed_ghost mixedQ _)

example : ¬ H .execute sameSigmas mixedQ
    (.ifProof (.base .u32) (.dfst (.var 0))
      (.finite (.uint 1)) (.finite (.uint 0))) (.base .u32) :=
  fun h => match h with
    | .ifProof (_ha) (_ba) (_hc) hq (_hl) (_hr) => hq

-- Runtime relevance alone cannot expose an equality-bearing product operand.
def evidenceProduct : Indexed.Ty 0 :=
  .product (.eq (.uint 0) (.uint 0)) (.refine .u32 (.var 0) (.var 0))
def evidenceContext : Dependent.Context 1 := .snoc empty evidenceProduct
def evidenceQ : Quantities 1 := extendWith emptyQ .run

theorem evidenceContext_formed : Dependent.Context.WellFormed evidenceContext :=
  .snoc .nil (.product (.eq .uint .uint) (.refine (.var rfl) (.var rfl)))

example : Allowed .execute evidenceQ (.value (.snd (.var 0))) := True.intro

theorem evidenceProduct_index_rejected :
    ¬ IndexHasType evidenceContext (.value (.snd (.var 0))) .u32 :=
  fun h => match h with
    | .value (.snd (.var ba)) => ba.1

example : ¬ H .execute evidenceContext evidenceQ
    (.finite (.value (.snd (.var 0)))) (.base .u32) :=
  fun h => match h with | .finite hi (_hq) => evidenceProduct_index_rejected hi

example : ¬ H .execute evidenceContext evidenceQ (.var 0)
    (Indexed.rename Fin.succ evidenceProduct) := fun h => h.runtimeType.1

-- General Ghost terms can inspect the product; index operands keep the guard.
example : H .ghost evidenceContext evidenceQ
    (.value (.snd (.var 0))) (.base .u32) :=
  .value (.snd (.var (evidenceContext_formed.lookup 0) True.intro True.intro))

example : ¬ H .ghost evidenceContext evidenceQ
    (.finite (.value (.snd (.var 0)))) (.base .u32) :=
  fun h => match h with | .finite hi (_hq) => evidenceProduct_index_rejected hi

-- Extending shared syntax does not add dependent elimination to finite typing.
example {Γ : Finite.Context n} {t : Finite.Term n} {a : Finite.Ty} :
    ¬ Finite.HasType Γ (.value t) a := fun h => nomatch h

example {Γ : Finite.Context n} {t : Finite.Term n} {a : Finite.Ty} :
    ¬ Finite.HasType Γ (.dfst t) a := fun h => nomatch h

-- Raw binding equations pin every local and free index across four binders.
def nested : Indexed.Ty 1 :=
  .sigma .bool (.refine .u32
    (.letIn .u32 (.value (.var 2))
      (.case .u32 (.inl .bool (.var 0))
        (.add (.var 0) (.value (.var 4))) (.dfst (.var 4))))
    (.cond (.var 1) (.dfst (.var 2)) (.var 0)))

example : Indexed.rename Fin.succ nested =
    .sigma .bool (.refine .u32
      (.letIn .u32 (.value (.var 3))
        (.case .u32 (.inl .bool (.var 0))
          (.add (.var 0) (.value (.var 5))) (.dfst (.var 5))))
      (.cond (.var 1) (.dfst (.var 3)) (.var 0))) := rfl

def replacement : Substitution 1 1 :=
  Fin.cases (.pair (.var 0) (.var 0)) Fin.elim0

example : Indexed.subst replacement nested =
    .sigma .bool (.refine .u32
      (.letIn .u32 (.value (.pair (.var 2) (.var 2)))
        (.case .u32 (.inl .bool (.var 0))
          (.add (.var 0) (.value (.pair (.var 4) (.var 4))))
          (.dfst (.pair (.var 4) (.var 4)))))
      (.cond (.var 1) (.dfst (.pair (.var 2) (.var 2))) (.var 0))) := rfl

example : Indexed.instantiate nested
    (.pair (.uint 7) (.boolean true) : Finite.Term 0) =
    .sigma .bool (.refine .u32
      (.letIn .u32 (.value (.pair (.uint 7) (.boolean true)))
        (.case .u32 (.inl .bool (.var 0))
          (.add (.var 0) (.value (.pair (.uint 7) (.boolean true))))
          (.dfst (.pair (.uint 7) (.boolean true)))))
      (.cond (.var 1) (.dfst (.pair (.uint 7) (.boolean true))) (.var 0))) := rfl

#print axioms Dependent.IndexHasSchema.rename
#print axioms Dependent.IndexHasSchema.weaken
#print axioms Dependent.IndexHasSchema.branchType
#print axioms Dependent.IndexHasSchema.wellFormed

end DependentIndexTest
