import AgentWasm.Substitution

namespace AgentWasm.Finite.Phased

inductive Phase where
  | execute | ghost
  deriving DecidableEq, Repr

inductive Relevance where
  | run | erase
  deriving DecidableEq, Repr

abbrev Quantities (n : Nat) := Fin n → Relevance

def extend (q : Quantities n) : Quantities (n + 1) := Fin.cases .run q

def Accessible : Phase → Relevance → Prop
  | .execute, .run => True
  | .execute, .erase => False
  | .ghost, .run | .ghost, .erase => True

/-- This finite syntax has runtime lets and case payload binders only. -/
def Allowed (p : Phase) (q : Quantities n) : Term n → Prop
  | .var i => Accessible p (q i)
  | .uint (_arg1) | .boolean (_arg2) => True
  | .add a b | .cmp (_arg1) a b | .pair a b => Allowed p q a ∧ Allowed p q b
  | .cond c a b => Allowed p q c ∧ Allowed p q a ∧ Allowed p q b
  | .fst a | .snd a | .inl (_arg1) a | .inr (_arg2) a | .ann a (_arg3) => Allowed p q a
  | .case (_arg1) s a b =>
      Allowed p q s ∧ Allowed p (extend q) a ∧ Allowed p (extend q) b
  | .letIn (_arg1) v body => Allowed p q v ∧ Allowed p (extend q) body

/-- Both typing and phase access are required; types remain non-dependent. -/
def HasType (p : Phase) (Γ : Context n) (q : Quantities n)
    (t : Term n) (a : Ty) : Prop := Finite.HasType Γ t a ∧ Allowed p q t

def RenamingPreserves (p : Phase) (q : Quantities n) (r : Quantities m)
    (ρ : Renaming n m) : Prop := ∀ i, Accessible p (q i) → Accessible p (r (ρ i))

theorem liftRen_preserves {p : Phase} {q : Quantities n} {r : Quantities m}
    {ρ : Renaming n m} (h : RenamingPreserves p q r ρ) :
    RenamingPreserves p (extend q) (extend r) (liftRen ρ) :=
  Fin.cases (fun h => h) h

theorem Allowed.rename {p : Phase} {q : Quantities n} {t : Term n}
    (ht : Allowed p q t) {r : Quantities m} (ρ : Renaming n m)
    (hρ : RenamingPreserves p q r ρ) : Allowed p r (Finite.rename ρ t) :=
  match t with
  | .var i => hρ i ht
  | .uint (_arg1) | .boolean (_arg2) => True.intro
  | .add (_arg1) (_arg2) | .cmp (_arg3) (_arg4) (_arg5) | .pair (_arg6) (_arg7) =>
      ⟨ht.1.rename ρ hρ, ht.2.rename ρ hρ⟩
  | .cond (_arg1) (_arg2) (_arg3) =>
      ⟨ht.1.rename ρ hρ, ht.2.1.rename ρ hρ, ht.2.2.rename ρ hρ⟩
  | .fst a | .snd a | .inl (_ty) a | .inr (_ty) a | .ann a (_ty) =>
      Allowed.rename (t := a) ht ρ hρ
  | .case (_arg1) (_arg2) (_arg3) (_arg4) => ⟨ht.1.rename ρ hρ,
      ht.2.1.rename (liftRen ρ) (liftRen_preserves hρ),
      ht.2.2.rename (liftRen ρ) (liftRen_preserves hρ)⟩
  | .letIn (_arg1) (_arg2) (_arg3) =>
      ⟨ht.1.rename ρ hρ, ht.2.rename (liftRen ρ) (liftRen_preserves hρ)⟩
termination_by structural t

theorem HasType.rename {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Ty} (ht : HasType p Γ q t a)
    {Δ : Context m} {r : Quantities m} (ρ : Renaming n m)
    (hΓ : Finite.RenamingPreserves Γ Δ ρ) (hq : RenamingPreserves p q r ρ) :
    HasType p Δ r (Finite.rename ρ t) a :=
  ⟨ht.1.rename ρ hΓ, ht.2.rename ρ hq⟩

theorem HasType.weaken {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Ty} (ht : HasType p Γ q t a) (b : Ty) :
    HasType p (Finite.extend Γ b) (extend q) (Finite.rename Fin.succ t) a :=
  ht.rename Fin.succ (fun (_i) => rfl) (fun (_i) h => h)

/-- All replacements type check; only accessible slots need phase access. -/
def SubstitutionPreserves (p : Phase) (Γ : Context n) (q : Quantities n)
    (Δ : Context m) (r : Quantities m) (σ : Substitution n m) : Prop :=
  Finite.SubstitutionPreserves Γ Δ σ ∧
    ∀ i, Accessible p (q i) → Allowed p r (σ i)

theorem liftSub_allowed {p : Phase} {q : Quantities n} {r : Quantities m}
    {σ : Substitution n m}
    (h : ∀ i, Accessible p (q i) → Allowed p r (σ i)) :
    ∀ i, Accessible p (extend q i) → Allowed p (extend r) (liftSub σ i) :=
  Fin.cases (fun h => h)
    (fun i hi => (h i hi).rename Fin.succ (fun (_i) h => h))

theorem liftSub_preserves {p : Phase} {Γ : Context n} {q : Quantities n}
    {Δ : Context m} {r : Quantities m} {σ : Substitution n m}
    (h : SubstitutionPreserves p Γ q Δ r σ) (a : Ty) :
    SubstitutionPreserves p (Finite.extend Γ a) (extend q)
      (Finite.extend Δ a) (extend r) (liftSub σ) :=
  ⟨Finite.liftSub_preserves h.1 a, liftSub_allowed h.2⟩

theorem Allowed.subst {p : Phase} {q : Quantities n} {t : Term n}
    (ht : Allowed p q t) {r : Quantities m} (σ : Substitution n m)
    (hσ : ∀ i, Accessible p (q i) → Allowed p r (σ i)) :
    Allowed p r (Finite.subst σ t) :=
  match t with
  | .var i => hσ i ht
  | .uint (_arg1) | .boolean (_arg2) => True.intro
  | .add (_arg1) (_arg2) | .cmp (_arg3) (_arg4) (_arg5) | .pair (_arg6) (_arg7) =>
      ⟨ht.1.subst σ hσ, ht.2.subst σ hσ⟩
  | .cond (_arg1) (_arg2) (_arg3) =>
      ⟨ht.1.subst σ hσ, ht.2.1.subst σ hσ, ht.2.2.subst σ hσ⟩
  | .fst a | .snd a | .inl (_ty) a | .inr (_ty) a | .ann a (_ty) =>
      Allowed.subst (t := a) ht σ hσ
  | .case (_arg1) (_arg2) (_arg3) (_arg4) => ⟨ht.1.subst σ hσ,
      ht.2.1.subst (liftSub σ) (liftSub_allowed hσ),
      ht.2.2.subst (liftSub σ) (liftSub_allowed hσ)⟩
  | .letIn (_arg1) (_arg2) (_arg3) =>
      ⟨ht.1.subst σ hσ, ht.2.subst (liftSub σ) (liftSub_allowed hσ)⟩
termination_by structural t

theorem HasType.subst {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Ty} (ht : HasType p Γ q t a)
    {Δ : Context m} {r : Quantities m} (σ : Substitution n m)
    (hσ : SubstitutionPreserves p Γ q Δ r σ) :
    HasType p Δ r (Finite.subst σ t) a :=
  ⟨ht.1.subst σ hσ.1, ht.2.subst σ hσ.2⟩

theorem HasType.instantiate {p : Phase} {Γ : Context n} {q : Quantities n}
    {body : Term (n + 1)} {v : Term n} {a b : Ty}
    (hb : HasType p (Finite.extend Γ a) (extend q) body b)
    (hv : HasType p Γ q v a) : HasType p Γ q (Finite.instantiate body v) b :=
  hb.subst (single v) ⟨Fin.cases hv.1 (fun (_i) => Finite.HasType.var),
    Fin.cases (fun (_h) => hv.2) (fun (_i) h => h)⟩

theorem accessible_ghost (q : Relevance) : Accessible .ghost q :=
  match q with
  | .run | .erase => True.intro

theorem allowed_ghost (q : Quantities n) (t : Term n) : Allowed .ghost q t :=
  match t with
  | .var i => accessible_ghost (q i)
  | .uint (_arg1) | .boolean (_arg2) => True.intro
  | .add a b | .cmp (_arg1) a b | .pair a b => ⟨allowed_ghost q a, allowed_ghost q b⟩
  | .cond c a b => ⟨allowed_ghost q c, allowed_ghost q a, allowed_ghost q b⟩
  | .fst a | .snd a | .inl (_arg1) a | .inr (_arg2) a | .ann a (_arg3) => allowed_ghost q a
  | .case (_arg1) s a b =>
      ⟨allowed_ghost q s, allowed_ghost (extend q) a, allowed_ghost (extend q) b⟩
  | .letIn (_arg1) v body => ⟨allowed_ghost q v, allowed_ghost (extend q) body⟩

theorem HasType.ghost {Γ : Context n} {q : Quantities n} {t : Term n} {a : Ty}
    (ht : Finite.HasType Γ t a) : HasType .ghost Γ q t a :=
  ⟨ht, allowed_ghost q t⟩

theorem erased_var_rejected {Γ : Context n} {q : Quantities n} {i : Fin n}
    {a : Ty} (hi : q i = .erase) : ¬ HasType .execute Γ q (.var i) a :=
  fun ht => Eq.mp (congrArg (Accessible .execute) hi) ht.2

end AgentWasm.Finite.Phased
