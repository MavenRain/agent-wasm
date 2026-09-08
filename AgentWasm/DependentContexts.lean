import AgentWasm.IndexedTypes

namespace AgentWasm.Dependent

open Finite

/-- Each declaration is scoped over its preceding telescope. -/
inductive Context : Nat → Type where
  | nil : Context 0
  | snoc : Context n → Indexed.Ty n → Context (n + 1)

/-- Expose a declaration in the scope of the entire telescope. -/
def lookup : Context n → Fin n → Indexed.Ty n
  | .nil, i => Fin.elim0 i
  | .snoc Γ a, i => Fin.cases (Indexed.rename Fin.succ a)
      (fun j => Indexed.rename Fin.succ (lookup Γ j)) i

theorem rename_weaken (a : Indexed.Ty n) (ρ : Renaming n m) :
    Indexed.rename (liftRen ρ) (Indexed.rename Fin.succ a) =
      Indexed.rename Fin.succ (Indexed.rename ρ a) :=
  Eq.trans (Indexed.rename_composition a Fin.succ (liftRen ρ)
    (fun i => (ρ i).succ) (fun (_i) => rfl))
    (Indexed.rename_composition a ρ Fin.succ
      (fun i => (ρ i).succ) (fun (_i) => rfl)).symm

/-- Renamings preserve dependent declaration types in their current scopes. -/
def RenamingPreserves (Γ : Context n) (Δ : Context m)
    (ρ : Renaming n m) : Prop :=
  ∀ i, lookup Δ (ρ i) = Indexed.rename ρ (lookup Γ i)

theorem liftRen_preserves {Γ : Context n} {Δ : Context m}
    {ρ : Renaming n m} (hρ : RenamingPreserves Γ Δ ρ) (a : Indexed.Ty n) :
    RenamingPreserves (.snoc Γ a) (.snoc Δ (Indexed.rename ρ a)) (liftRen ρ) :=
  Fin.cases (rename_weaken a ρ).symm
    (fun i => Eq.trans (congrArg (Indexed.rename Fin.succ) (hρ i))
      (rename_weaken (lookup Γ i) ρ).symm)

/-- Only declarations explicitly having a base type enter the finite index
language. Equality evidence and dependent payloads are not coerced to shapes. -/
inductive IndexHasType : Context n → Finite.Term n → Finite.Ty → Prop where
  | var : lookup Γ i = .base a → IndexHasType Γ (.var i) a
  | uint : IndexHasType Γ (.uint v) .u32
  | boolean : IndexHasType Γ (.boolean v) .bool
  | add : IndexHasType Γ a .u32 → IndexHasType Γ b .u32 →
      IndexHasType Γ (.add a b) .u32
  | cmp : IndexHasType Γ a .u32 → IndexHasType Γ b .u32 →
      IndexHasType Γ (.cmp op a b) .bool
  | cond : IndexHasType Γ c .bool → IndexHasType Γ a r →
      IndexHasType Γ b r → IndexHasType Γ (.cond c a b) r
  | pair : IndexHasType Γ a x → IndexHasType Γ b y →
      IndexHasType Γ (.pair a b) (.product x y)
  | fst : IndexHasType Γ a (.product x y) → IndexHasType Γ (.fst a) x
  | snd : IndexHasType Γ a (.product x y) → IndexHasType Γ (.snd a) y
  | inl : IndexHasType Γ a x → IndexHasType Γ (.inl y a) (.sum x y)
  | inr : IndexHasType Γ b y → IndexHasType Γ (.inr x b) (.sum x y)
  | case : IndexHasType Γ s (.sum x y) →
      IndexHasType (.snoc Γ (.base x)) a r →
      IndexHasType (.snoc Γ (.base y)) b r →
      IndexHasType Γ (.case r s a b) r
  | letIn : IndexHasType Γ v a →
      IndexHasType (.snoc Γ (.base a)) body b →
      IndexHasType Γ (.letIn a v body) b
  | ann : IndexHasType Γ t a → IndexHasType Γ (.ann t a) a

theorem IndexHasType.rename {Γ : Context n} {t : Finite.Term n} {a : Finite.Ty}
    (ht : IndexHasType Γ t a) {Δ : Context m} (ρ : Renaming n m)
    (hρ : RenamingPreserves Γ Δ ρ) :
    IndexHasType Δ (Finite.rename ρ t) a :=
  match ht with
  | .var hi => .var (Eq.trans (hρ _) (congrArg (Indexed.rename ρ) hi))
  | .uint => .uint
  | .boolean => .boolean
  | .add ha hb => .add (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .cmp ha hb => .cmp (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .cond hc ha hb => .cond (hc.rename ρ hρ) (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .pair ha hb => .pair (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .fst ha => .fst (ha.rename ρ hρ)
  | .snd ha => .snd (ha.rename ρ hρ)
  | .inl ha => .inl (ha.rename ρ hρ)
  | .inr hb => .inr (hb.rename ρ hρ)
  | .case hs ha hb => .case (hs.rename ρ hρ)
      (ha.rename (liftRen ρ) (liftRen_preserves hρ _))
      (hb.rename (liftRen ρ) (liftRen_preserves hρ _))
  | .letIn hv hb => .letIn (hv.rename ρ hρ)
      (hb.rename (liftRen ρ) (liftRen_preserves hρ _))
  | .ann ht => .ann (ht.rename ρ hρ)

theorem IndexHasType.weaken {Γ : Context n} {t : Finite.Term n} {a : Finite.Ty}
    (ht : IndexHasType Γ t a) (b : Indexed.Ty n) :
    IndexHasType (.snoc Γ b) (Finite.rename Fin.succ t) a :=
  ht.rename Fin.succ (fun (_i) => rfl)

/-- Formation checks indices against the full dependent telescope. The index
language and the refinement and Sigma domains remain finite. -/
inductive WellFormed : Context n → Indexed.Ty n → Prop where
  | base : WellFormed Γ (.base a)
  | eq : IndexHasType Γ l .u32 → IndexHasType Γ r .u32 →
      WellFormed Γ (.eq l r)
  | product : WellFormed Γ a → WellFormed Γ b → WellFormed Γ (.product a b)
  | sum : Indexed.BranchType a → Indexed.BranchType b →
      WellFormed Γ a → WellFormed Γ b → WellFormed Γ (.sum a b)
  | refine : IndexHasType (.snoc Γ (.base a)) l .u32 →
      IndexHasType (.snoc Γ (.base a)) r .u32 → WellFormed Γ (.refine a l r)
  | sigma : Indexed.BranchType b → WellFormed (.snoc Γ (.base a)) b →
      WellFormed Γ (.sigma a b)

theorem WellFormed.rename {Γ : Context n} {a : Indexed.Ty n}
    (ha : WellFormed Γ a) {Δ : Context m} (ρ : Renaming n m)
    (hρ : RenamingPreserves Γ Δ ρ) :
    WellFormed Δ (Indexed.rename ρ a) :=
  match ha with
  | .base => .base
  | .eq hl hr => .eq (hl.rename ρ hρ) (hr.rename ρ hρ)
  | .product ha hb => .product (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .sum ba bb ha hb => .sum
      (Eq.mpr (Indexed.branch_rename _ ρ) ba)
      (Eq.mpr (Indexed.branch_rename _ ρ) bb)
      (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .refine hl hr => .refine
      (hl.rename (liftRen ρ) (liftRen_preserves hρ _))
      (hr.rename (liftRen ρ) (liftRen_preserves hρ _))
  | .sigma bb hb => .sigma
      (Eq.mpr (Indexed.branch_rename _ (liftRen ρ)) bb)
      (hb.rename (liftRen ρ) (liftRen_preserves hρ _))

theorem WellFormed.weaken {Γ : Context n} {a : Indexed.Ty n}
    (ha : WellFormed Γ a) (b : Indexed.Ty n) :
    WellFormed (.snoc Γ b) (Indexed.rename Fin.succ a) :=
  ha.rename Fin.succ (fun (_i) => rfl)

/-- Every declaration is formed using only its preceding declarations. -/
inductive Context.WellFormed : Context n → Prop where
  | nil : Context.WellFormed .nil
  | snoc : Context.WellFormed Γ → Dependent.WellFormed Γ a →
      Context.WellFormed (.snoc Γ a)

/-- Looking up an older entry includes all intervening binder shifts. -/
theorem Context.WellFormed.lookup {Γ : Context n}
    (hΓ : Context.WellFormed Γ) (i : Fin n) :
    Dependent.WellFormed Γ (Dependent.lookup Γ i) :=
  match n, Γ, hΓ, i with
  | 0, .nil, .nil, i => Fin.elim0 i
  | _ + 1, .snoc _ _, .snoc hΓ ha, i =>
      Fin.cases (ha.weaken _) (fun j => (hΓ.lookup j).weaken _) i

end AgentWasm.Dependent
