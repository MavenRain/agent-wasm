/- A mathematical binding model, not verification of the OCaml implementation. -/
namespace AgentWasm.Finite

private theorem congrArg2 (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' :=
  Eq.trans (congrArg (fun x => f x b) ha) (congrArg (f a') hb)

private theorem congrArg3 (f : α → β → γ → δ)
    {a a' : α} {b b' : β} {c c' : γ} (ha : a = a') (hb : b = b')
    (hc : c = c') : f a b c = f a' b' c' :=
  Eq.trans (congrArg (fun x => f x b c) ha) (congrArg2 (f a') hb hc)

inductive Ty where
  | u32 | bool
  | product (left right : Ty)
  | sum (left right : Ty)
  deriving DecidableEq, Repr

inductive Comparison where
  | eq | lt | le
  deriving DecidableEq, Repr

/-- Scope is intrinsic; typing is separate. The newest binder has index 0. -/
inductive Term : Nat → Type where
  | var : Fin n → Term n
  | uint : Fin (2 ^ 32) → Term n
  | boolean : Bool → Term n
  | add : Term n → Term n → Term n
  | cmp : Comparison → Term n → Term n → Term n
  | cond : Term n → Term n → Term n → Term n
  | pair : Term n → Term n → Term n
  | fst : Term n → Term n
  | snd : Term n → Term n
  | inl : Ty → Term n → Term n
  | inr : Ty → Term n → Term n
  | case : Ty → Term n → Term (n + 1) → Term (n + 1) → Term n
  | letIn : Ty → Term n → Term (n + 1) → Term n
  | ann : Term n → Ty → Term n
  deriving Repr

abbrev Context (n : Nat) := Fin n → Ty
abbrev Renaming (n m : Nat) := Fin n → Fin m
abbrev Substitution (n m : Nat) := Fin n → Term m

def extend (Γ : Context n) (a : Ty) : Context (n + 1) := Fin.cases a Γ

/-- Keep the new binder fixed, moving only variables outside it. -/
def liftRen (ρ : Renaming n m) : Renaming (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def rename (ρ : Renaming n m) : Term n → Term m
  | .var i => .var (ρ i)
  | .uint v => .uint v
  | .boolean v => .boolean v
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .cmp op a b => .cmp op (rename ρ a) (rename ρ b)
  | .cond c a b => .cond (rename ρ c) (rename ρ a) (rename ρ b)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst a => .fst (rename ρ a)
  | .snd a => .snd (rename ρ a)
  | .inl b a => .inl b (rename ρ a)
  | .inr a b => .inr a (rename ρ b)
  | .case r s a b =>
    .case r (rename ρ s) (rename (liftRen ρ) a) (rename (liftRen ρ) b)
  | .letIn a v body => .letIn a (rename ρ v) (rename (liftRen ρ) body)
  | .ann t a => .ann (rename ρ t) a

/-- Lift open replacements when crossing a binder, avoiding capture. -/
def liftSub (σ : Substitution n m) : Substitution (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def subst (σ : Substitution n m) : Term n → Term m
  | .var i => σ i
  | .uint v => .uint v
  | .boolean v => .boolean v
  | .add a b => .add (subst σ a) (subst σ b)
  | .cmp op a b => .cmp op (subst σ a) (subst σ b)
  | .cond c a b => .cond (subst σ c) (subst σ a) (subst σ b)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst a => .fst (subst σ a)
  | .snd a => .snd (subst σ a)
  | .inl b a => .inl b (subst σ a)
  | .inr a b => .inr a (subst σ b)
  | .case r s a b =>
    .case r (subst σ s) (subst (liftSub σ) a) (subst (liftSub σ) b)
  | .letIn a v body => .letIn a (subst σ v) (subst (liftSub σ) body)
  | .ann t a => .ann (subst σ t) a

/-- Remove the newest binder, replacing it with a term in the outer scope. -/
def single (a : Term n) : Substitution (n + 1) n := Fin.cases a Term.var

def instantiate (body : Term (n + 1)) (a : Term n) : Term n :=
  subst (single a) body

theorem liftRen_identity {ρ : Renaming n n} (h : ∀ i, ρ i = i) :
    ∀ i, liftRen ρ i = i :=
  Fin.cases rfl (fun i => congrArg Fin.succ (h i))

/-- Pointwise identity also holds below arbitrarily many binders. -/
theorem rename_identity (t : Term n) (ρ : Renaming n n) (h : ∀ i, ρ i = i) :
    rename ρ t = t :=
  match t with
  | .var i => congrArg Term.var (h i)
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add (rename_identity a ρ h) (rename_identity b ρ h)
  | .cmp op a b =>
    congrArg2 (Term.cmp op) (rename_identity a ρ h) (rename_identity b ρ h)
  | .cond c a b => congrArg3 Term.cond
      (rename_identity c ρ h) (rename_identity a ρ h) (rename_identity b ρ h)
  | .pair a b => congrArg2 Term.pair (rename_identity a ρ h) (rename_identity b ρ h)
  | .fst a => congrArg Term.fst (rename_identity a ρ h)
  | .snd a => congrArg Term.snd (rename_identity a ρ h)
  | .inl b a => congrArg (Term.inl b) (rename_identity a ρ h)
  | .inr a b => congrArg (Term.inr a) (rename_identity b ρ h)
  | .case r s a b => congrArg3 (Term.case r) (rename_identity s ρ h)
      (rename_identity a (liftRen ρ) (liftRen_identity h))
      (rename_identity b (liftRen ρ) (liftRen_identity h))
  | .letIn a v body => congrArg2 (Term.letIn a) (rename_identity v ρ h)
      (rename_identity body (liftRen ρ) (liftRen_identity h))
  | .ann t a => congrArg (fun v => Term.ann v a) (rename_identity t ρ h)

theorem liftSub_identity {σ : Substitution n n} (h : ∀ i, σ i = .var i) :
    ∀ i, liftSub σ i = .var i :=
  Fin.cases rfl (fun i => congrArg (rename Fin.succ) (h i))

/-- Identity substitution is syntax equality, including scoped untyped terms. -/
theorem subst_identity (t : Term n) (σ : Substitution n n)
    (h : ∀ i, σ i = .var i) : subst σ t = t :=
  match t with
  | .var i => h i
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add (subst_identity a σ h) (subst_identity b σ h)
  | .cmp op a b =>
    congrArg2 (Term.cmp op) (subst_identity a σ h) (subst_identity b σ h)
  | .cond c a b => congrArg3 Term.cond
      (subst_identity c σ h) (subst_identity a σ h) (subst_identity b σ h)
  | .pair a b => congrArg2 Term.pair (subst_identity a σ h) (subst_identity b σ h)
  | .fst a => congrArg Term.fst (subst_identity a σ h)
  | .snd a => congrArg Term.snd (subst_identity a σ h)
  | .inl b a => congrArg (Term.inl b) (subst_identity a σ h)
  | .inr a b => congrArg (Term.inr a) (subst_identity b σ h)
  | .case r s a b => congrArg3 (Term.case r) (subst_identity s σ h)
      (subst_identity a (liftSub σ) (liftSub_identity h))
      (subst_identity b (liftSub σ) (liftSub_identity h))
  | .letIn a v body => congrArg2 (Term.letIn a) (subst_identity v σ h)
      (subst_identity body (liftSub σ) (liftSub_identity h))
  | .ann t a => congrArg (fun v => Term.ann v a) (subst_identity t σ h)

theorem rename_id (t : Term n) : rename id t = t :=
  rename_identity t id (fun (_i) => rfl)

theorem subst_id (t : Term n) : subst Term.var t = t :=
  subst_identity t Term.var (fun (_i) => rfl)

inductive HasType : Context n → Term n → Ty → Prop where
  | var : HasType Γ (.var i) (Γ i)
  | uint : HasType Γ (.uint v) .u32
  | boolean : HasType Γ (.boolean v) .bool
  | add : HasType Γ a .u32 → HasType Γ b .u32 → HasType Γ (.add a b) .u32
  | cmp : HasType Γ a .u32 → HasType Γ b .u32 → HasType Γ (.cmp op a b) .bool
  | cond : HasType Γ c .bool → HasType Γ a r → HasType Γ b r →
      HasType Γ (.cond c a b) r
  | pair : HasType Γ a x → HasType Γ b y → HasType Γ (.pair a b) (.product x y)
  | fst : HasType Γ a (.product x y) → HasType Γ (.fst a) x
  | snd : HasType Γ a (.product x y) → HasType Γ (.snd a) y
  | inl : HasType Γ a x → HasType Γ (.inl y a) (.sum x y)
  | inr : HasType Γ b y → HasType Γ (.inr x b) (.sum x y)
  | case : HasType Γ s (.sum x y) → HasType (extend Γ x) a r →
      HasType (extend Γ y) b r → HasType Γ (.case r s a b) r
  | letIn : HasType Γ v a → HasType (extend Γ a) body b →
      HasType Γ (.letIn a v body) b
  | ann : HasType Γ t a → HasType Γ (.ann t a) a

def RenamingPreserves (Γ : Context n) (Δ : Context m) (ρ : Renaming n m) : Prop :=
  ∀ i, Δ (ρ i) = Γ i

theorem liftRen_preserves {Γ : Context n} {Δ : Context m} {ρ : Renaming n m}
    (h : RenamingPreserves Γ Δ ρ) (a : Ty) :
    RenamingPreserves (extend Γ a) (extend Δ a) (liftRen ρ) :=
  Fin.cases rfl h

/-- Renaming preserves the extrinsic typing derivation for every constructor. -/
theorem HasType.rename {Γ : Context n} {t : Term n} {a : Ty}
    (ht : HasType Γ t a) {Δ : Context m} (ρ : Renaming n m)
    (hρ : RenamingPreserves Γ Δ ρ) : HasType Δ (Finite.rename ρ t) a :=
  match ht with
  | .var => (hρ _) ▸ HasType.var
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

theorem HasType.weaken {Γ : Context n} {t : Term n} {a : Ty}
    (ht : HasType Γ t a) (b : Ty) :
    HasType (extend Γ b) (Finite.rename Fin.succ t) a :=
  ht.rename Fin.succ (fun (_i) => rfl)

def SubstitutionPreserves (Γ : Context n) (Δ : Context m)
    (σ : Substitution n m) : Prop := ∀ i, HasType Δ (σ i) (Γ i)

theorem liftSub_preserves {Γ : Context n} {Δ : Context m} {σ : Substitution n m}
    (h : SubstitutionPreserves Γ Δ σ) (a : Ty) :
    SubstitutionPreserves (extend Γ a) (extend Δ a) (liftSub σ) :=
  Fin.cases HasType.var (fun i => (h i).weaken a)

/-- Simultaneous typed substitution, including open replacements under binders. -/
theorem HasType.subst {Γ : Context n} {t : Term n} {a : Ty}
    (ht : HasType Γ t a) {Δ : Context m} (σ : Substitution n m)
    (hσ : SubstitutionPreserves Γ Δ σ) : HasType Δ (Finite.subst σ t) a :=
  match ht with
  | .var => hσ _
  | .uint => .uint
  | .boolean => .boolean
  | .add ha hb => .add (ha.subst σ hσ) (hb.subst σ hσ)
  | .cmp ha hb => .cmp (ha.subst σ hσ) (hb.subst σ hσ)
  | .cond hc ha hb => .cond (hc.subst σ hσ) (ha.subst σ hσ) (hb.subst σ hσ)
  | .pair ha hb => .pair (ha.subst σ hσ) (hb.subst σ hσ)
  | .fst ha => .fst (ha.subst σ hσ)
  | .snd ha => .snd (ha.subst σ hσ)
  | .inl ha => .inl (ha.subst σ hσ)
  | .inr hb => .inr (hb.subst σ hσ)
  | .case hs ha hb => .case (hs.subst σ hσ)
      (ha.subst (liftSub σ) (liftSub_preserves hσ _))
      (hb.subst (liftSub σ) (liftSub_preserves hσ _))
  | .letIn hv hb => .letIn (hv.subst σ hσ)
      (hb.subst (liftSub σ) (liftSub_preserves hσ _))
  | .ann ht => .ann (ht.subst σ hσ)

/-- Binder-removing substitution for let and case reduction preserves typing. -/
theorem HasType.instantiate {Γ : Context n} {body : Term (n + 1)}
    {v : Term n} {a b : Ty} (hb : HasType (extend Γ a) body b)
    (hv : HasType Γ v a) : HasType Γ (Finite.instantiate body v) b :=
  hb.subst (single v) (Fin.cases hv (fun (_i) => HasType.var))

end AgentWasm.Finite
