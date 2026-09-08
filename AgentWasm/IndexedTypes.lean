import AgentWasm.Phases
import AgentWasm.BindingLaws

/- Indexed type formation over finite contexts, not dependent term typing. -/
namespace AgentWasm.Indexed

open Finite

private theorem congrArg2 (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' :=
  Eq.trans (congrArg (fun x => f x b) ha) (congrArg (f a') hb)

/-- Domains stay finite. Only equality endpoints and Sigma ranges depend. -/
inductive Ty : Nat → Type where
  | base : Finite.Ty → Ty n
  | eq : Term n → Term n → Ty n
  | product : Ty n → Ty n → Ty n
  | sum : Ty n → Ty n → Ty n
  | refine : Finite.Ty → Term (n + 1) → Term (n + 1) → Ty n
  | sigma : Finite.Ty → Ty (n + 1) → Ty n
  deriving Repr

def rename (ρ : Renaming n m) : Ty n → Ty m
  | .base a => .base a
  | .eq a b => .eq (Finite.rename ρ a) (Finite.rename ρ b)
  | .product a b => .product (rename ρ a) (rename ρ b)
  | .sum a b => .sum (rename ρ a) (rename ρ b)
  | .refine a l r =>
      .refine a (Finite.rename (liftRen ρ) l) (Finite.rename (liftRen ρ) r)
  | .sigma a b => .sigma a (rename (liftRen ρ) b)

/-- Refinement payloads and Sigma domains each introduce one index binder. -/
def subst (σ : Substitution n m) : Ty n → Ty m
  | .base a => .base a
  | .eq a b => .eq (Finite.subst σ a) (Finite.subst σ b)
  | .product a b => .product (subst σ a) (subst σ b)
  | .sum a b => .sum (subst σ a) (subst σ b)
  | .refine a l r =>
      .refine a (Finite.subst (liftSub σ) l) (Finite.subst (liftSub σ) r)
  | .sigma a b => .sigma a (subst (liftSub σ) b)

def instantiate (family : Ty (n + 1)) (value : Term n) : Ty n :=
  subst (single value) family

theorem rename_identity (a : Ty n) (ρ : Renaming n n) (h : ∀ i, ρ i = i) :
    rename ρ a = a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.rename_identity l ρ h) (Finite.rename_identity r ρ h)
  | .product a b => congrArg2 Ty.product
      (rename_identity a ρ h) (rename_identity b ρ h)
  | .sum a b => congrArg2 Ty.sum
      (rename_identity a ρ h) (rename_identity b ρ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.rename_identity l (liftRen ρ) (liftRen_identity h))
      (Finite.rename_identity r (liftRen ρ) (liftRen_identity h))
  | .sigma a b => congrArg (Ty.sigma a)
      (rename_identity b (liftRen ρ) (liftRen_identity h))

theorem subst_identity (a : Ty n) (σ : Substitution n n)
    (h : ∀ i, σ i = .var i) : subst σ a = a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.subst_identity l σ h) (Finite.subst_identity r σ h)
  | .product a b => congrArg2 Ty.product
      (subst_identity a σ h) (subst_identity b σ h)
  | .sum a b => congrArg2 Ty.sum
      (subst_identity a σ h) (subst_identity b σ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.subst_identity l (liftSub σ) (liftSub_identity h))
      (Finite.subst_identity r (liftSub σ) (liftSub_identity h))
  | .sigma a b => congrArg (Ty.sigma a)
      (subst_identity b (liftSub σ) (liftSub_identity h))

theorem rename_id (a : Ty n) : rename id a = a :=
  rename_identity a id (fun (_i) => rfl)

theorem subst_id (a : Ty n) : subst Term.var a = a :=
  subst_identity a Term.var (fun (_i) => rfl)

/-- Equality is ghost evidence; refinements retain only their finite payload. -/
def BranchType : Ty n → Prop
  | .base (_a) | .refine (_b) (_l) (_r) => True
  | .eq (_l) (_r) => False
  | .product a b | .sum a b => BranchType a ∧ BranchType b
  | .sigma (_a) b => BranchType b

theorem branch_rename (a : Ty n) (ρ : Renaming n m) :
    BranchType (rename ρ a) = BranchType a :=
  match a with
  | .base (_a) | .eq (_l) (_r) | .refine (_b) (_x) (_y) => rfl
  | .product a b | .sum a b =>
      congrArg2 And (branch_rename a ρ) (branch_rename b ρ)
  | .sigma (_a) b => branch_rename b (liftRen ρ)

theorem branch_subst (a : Ty n) (σ : Substitution n m) :
    BranchType (subst σ a) = BranchType a :=
  match a with
  | .base (_a) | .eq (_l) (_r) | .refine (_b) (_x) (_y) => rfl
  | .product a b | .sum a b =>
      congrArg2 And (branch_subst a σ) (branch_subst b σ)
  | .sigma (_a) b => branch_subst b (liftSub σ)

/-- Finite contexts give endpoint types. Their variables are checked in Ghost,
    where either relevance is accessible. No context type is erased to a shape. -/
inductive WellFormed : Context n → Ty n → Prop where
  | base : WellFormed Γ (.base a)
  | eq : Finite.HasType Γ l .u32 → Finite.HasType Γ r .u32 →
      WellFormed Γ (.eq l r)
  | product : WellFormed Γ a → WellFormed Γ b →
      WellFormed Γ (.product a b)
  | sum : BranchType a → BranchType b → WellFormed Γ a → WellFormed Γ b →
      WellFormed Γ (.sum a b)
  | refine : Finite.HasType (extend Γ a) l .u32 →
      Finite.HasType (extend Γ a) r .u32 → WellFormed Γ (.refine a l r)
  | sigma : BranchType b → WellFormed (extend Γ a) b →
      WellFormed Γ (.sigma a b)

theorem WellFormed.rename {Γ : Context n} {a : Ty n}
    (ha : WellFormed Γ a) {Δ : Context m} (ρ : Renaming n m)
    (hρ : Finite.RenamingPreserves Γ Δ ρ) :
    WellFormed Δ (Indexed.rename ρ a) :=
  match ha with
  | .base => .base
  | .eq hl hr => .eq (hl.rename ρ hρ) (hr.rename ρ hρ)
  | .product ha hb => .product (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .sum ba bb ha hb => .sum
      (Eq.mpr (branch_rename _ ρ) ba) (Eq.mpr (branch_rename _ ρ) bb)
      (ha.rename ρ hρ) (hb.rename ρ hρ)
  | .refine hl hr => .refine
      (hl.rename (liftRen ρ) (liftRen_preserves hρ _))
      (hr.rename (liftRen ρ) (liftRen_preserves hρ _))
  | .sigma bb hb => .sigma (Eq.mpr (branch_rename _ (liftRen ρ)) bb)
      (hb.rename (liftRen ρ) (liftRen_preserves hρ _))

theorem WellFormed.weaken {Γ : Context n} {a : Ty n}
    (ha : WellFormed Γ a) (b : Finite.Ty) :
    WellFormed (extend Γ b) (Indexed.rename Fin.succ a) :=
  ha.rename Fin.succ (fun (_i) => rfl)

/-- Typed finite replacements transform the indices and preserve formation. -/
theorem WellFormed.subst {Γ : Context n} {a : Ty n}
    (ha : WellFormed Γ a) {Δ : Context m} (σ : Substitution n m)
    (hσ : Finite.SubstitutionPreserves Γ Δ σ) :
    WellFormed Δ (Indexed.subst σ a) :=
  match ha with
  | .base => .base
  | .eq hl hr => .eq (hl.subst σ hσ) (hr.subst σ hσ)
  | .product ha hb => .product (ha.subst σ hσ) (hb.subst σ hσ)
  | .sum ba bb ha hb => .sum
      (Eq.mpr (branch_subst _ σ) ba) (Eq.mpr (branch_subst _ σ) bb)
      (ha.subst σ hσ) (hb.subst σ hσ)
  | .refine hl hr => .refine
      (hl.subst (liftSub σ) (liftSub_preserves hσ _))
      (hr.subst (liftSub σ) (liftSub_preserves hσ _))
  | .sigma bb hb => .sigma (Eq.mpr (branch_subst _ (liftSub σ)) bb)
      (hb.subst (liftSub σ) (liftSub_preserves hσ _))

theorem WellFormed.instantiate {Γ : Context n} {family : Ty (n + 1)}
    {value : Term n} {a : Finite.Ty} (hf : WellFormed (extend Γ a) family)
    (hv : Finite.HasType Γ value a) :
    WellFormed Γ (Indexed.instantiate family value) :=
  hf.subst (single value) (Fin.cases hv (fun (_i) => Finite.HasType.var))

/-- A Ghost typed replacement also preserves formation. The proof uses
only the finite typing component of its premise. -/
theorem WellFormed.subst_ghost {Γ : Context n} {a : Ty n}
    (ha : WellFormed Γ a) {Δ : Context m} {q : Phased.Quantities n}
    {r : Phased.Quantities m} (σ : Substitution n m)
    (hσ : Phased.SubstitutionPreserves .ghost Γ q Δ r σ) :
    WellFormed Δ (Indexed.subst σ a) := ha.subst σ hσ.1

/-- This representation function describes types, not compiler erasure. -/
def shape : Ty n → Option Finite.Ty
  | .base a | .refine a (_l) (_r) => some a
  | .eq (_l) (_r) => none
  | .product a b => (shape a).bind (fun x => (shape b).map (Finite.Ty.product x))
  | .sum a b => (shape a).bind (fun x => (shape b).map (Finite.Ty.sum x))
  | .sigma a b => (shape b).map (Finite.Ty.product a)

theorem shape_rename (a : Ty n) (ρ : Renaming n m) :
    shape (rename ρ a) = shape a :=
  match a with
  | .base (_a) | .eq (_l) (_r) | .refine (_b) (_x) (_y) => rfl
  | .product a b => congrArg2
      (fun x y => x.bind (fun l => y.map (Finite.Ty.product l)))
      (shape_rename a ρ) (shape_rename b ρ)
  | .sum a b => congrArg2
      (fun x y => x.bind (fun l => y.map (Finite.Ty.sum l)))
      (shape_rename a ρ) (shape_rename b ρ)
  | .sigma a b => congrArg (Option.map (Finite.Ty.product a))
      (shape_rename b (liftRen ρ))

theorem shape_subst (a : Ty n) (σ : Substitution n m) :
    shape (subst σ a) = shape a :=
  match a with
  | .base (_a) | .eq (_l) (_r) | .refine (_b) (_x) (_y) => rfl
  | .product a b => congrArg2
      (fun x y => x.bind (fun l => y.map (Finite.Ty.product l)))
      (shape_subst a σ) (shape_subst b σ)
  | .sum a b => congrArg2
      (fun x y => x.bind (fun l => y.map (Finite.Ty.sum l)))
      (shape_subst a σ) (shape_subst b σ)
  | .sigma a b => congrArg (Option.map (Finite.Ty.product a))
      (shape_subst b (liftSub σ))

theorem rename_composition (a : Ty n) (ρ : Renaming n m)
    (τ : Renaming m k) (κ : Renaming n k) (h : ∀ i, τ (ρ i) = κ i) :
    rename τ (rename ρ a) = rename κ a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.rename_composition l ρ τ κ h) (Finite.rename_composition r ρ τ κ h)
  | .product a b => congrArg2 Ty.product
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .sum a b => congrArg2 Ty.sum
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.rename_composition l (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))
      (Finite.rename_composition r (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))
  | .sigma a b => congrArg (Ty.sigma a)
      (rename_composition b (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))

theorem subst_renaming (a : Ty n) (ρ : Renaming n m)
    (σ : Substitution m k) (θ : Substitution n k) (h : ∀ i, σ (ρ i) = θ i) :
    subst σ (rename ρ a) = subst θ a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.subst_renaming l ρ σ θ h) (Finite.subst_renaming r ρ σ θ h)
  | .product a b => congrArg2 Ty.product
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .sum a b => congrArg2 Ty.sum
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.subst_renaming l (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (Finite.rename Fin.succ) (h i))))
      (Finite.subst_renaming r (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (Finite.rename Fin.succ) (h i))))
  | .sigma a b => congrArg (Ty.sigma a)
      (subst_renaming b (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (Finite.rename Fin.succ) (h i))))

theorem rename_substitution (a : Ty n) (σ : Substitution n m)
    (ρ : Renaming m k) (θ : Substitution n k)
    (h : ∀ i, Finite.rename ρ (σ i) = θ i) :
    rename ρ (subst σ a) = subst θ a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.rename_substitution l σ ρ θ h) (Finite.rename_substitution r σ ρ θ h)
  | .product a b => congrArg2 Ty.product
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .sum a b => congrArg2 Ty.sum
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.rename_substitution l (liftSub σ) (liftRen ρ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.rename_weaken (σ i) ρ)
          (congrArg (Finite.rename Fin.succ) (h i)))))
      (Finite.rename_substitution r (liftSub σ) (liftRen ρ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.rename_weaken (σ i) ρ)
          (congrArg (Finite.rename Fin.succ) (h i)))))
  | .sigma a b => congrArg (Ty.sigma a)
      (rename_substitution b (liftSub σ) (liftRen ρ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.rename_weaken (σ i) ρ)
          (congrArg (Finite.rename Fin.succ) (h i)))))

theorem subst_composition (a : Ty n) (σ : Substitution n m)
    (τ : Substitution m k) (θ : Substitution n k)
    (h : ∀ i, Finite.subst τ (σ i) = θ i) :
    subst τ (subst σ a) = subst θ a :=
  match a with
  | .base (_a) => rfl
  | .eq l r => congrArg2 Ty.eq
      (Finite.subst_composition l σ τ θ h) (Finite.subst_composition r σ τ θ h)
  | .product a b => congrArg2 Ty.product
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .sum a b => congrArg2 Ty.sum
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .refine a l r => congrArg2 (Ty.refine a)
      (Finite.subst_composition l (liftSub σ) (liftSub τ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.subst_weaken (σ i) τ)
          (congrArg (Finite.rename Fin.succ) (h i)))))
      (Finite.subst_composition r (liftSub σ) (liftSub τ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.subst_weaken (σ i) τ)
          (congrArg (Finite.rename Fin.succ) (h i)))))
  | .sigma a b => congrArg (Ty.sigma a)
      (subst_composition b (liftSub σ) (liftSub τ) (liftSub θ)
        (Fin.cases rfl (fun i => Eq.trans (Finite.subst_weaken (σ i) τ)
          (congrArg (Finite.rename Fin.succ) (h i)))))

theorem rename_comp (a : Ty n) (ρ : Renaming n m) (τ : Renaming m k) :
    rename τ (rename ρ a) = rename (fun i => τ (ρ i)) a :=
  rename_composition a ρ τ (fun i => τ (ρ i)) (fun (_i) => rfl)

theorem subst_rename (a : Ty n) (ρ : Renaming n m) (σ : Substitution m k) :
    subst σ (rename ρ a) = subst (fun i => σ (ρ i)) a :=
  subst_renaming a ρ σ (fun i => σ (ρ i)) (fun (_i) => rfl)

theorem rename_subst (a : Ty n) (σ : Substitution n m) (ρ : Renaming m k) :
    rename ρ (subst σ a) = subst (fun i => Finite.rename ρ (σ i)) a :=
  rename_substitution a σ ρ (fun i => Finite.rename ρ (σ i)) (fun (_i) => rfl)

theorem subst_comp (a : Ty n) (σ : Substitution n m) (τ : Substitution m k) :
    subst τ (subst σ a) = subst (fun i => Finite.subst τ (σ i)) a :=
  subst_composition a σ τ (fun i => Finite.subst τ (σ i)) (fun (_i) => rfl)

theorem instantiate_weaken (a : Ty n) (value : Term n) :
    instantiate (rename Fin.succ a) value = a :=
  Eq.trans (subst_renaming a Fin.succ (single value) Term.var
    (fun (_i) => rfl)) (subst_id a)

/-- Family instantiation commutes with substitutions into the outer context. -/
theorem subst_instantiate (family : Ty (n + 1)) (value : Term n)
    (σ : Substitution n m) :
    subst σ (instantiate family value) =
      instantiate (subst (liftSub σ) family) (Finite.subst σ value) :=
  Eq.trans (subst_comp family (single value) σ)
    (subst_composition family (liftSub σ) (single (Finite.subst σ value))
      (fun i => Finite.subst σ (single value i))
      (Fin.cases rfl (fun i =>
        Finite.instantiate_weaken (σ i) (Finite.subst σ value)))).symm

end AgentWasm.Indexed
