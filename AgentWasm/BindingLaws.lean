import AgentWasm.Substitution

namespace AgentWasm.Finite

private theorem congrArg2 (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' :=
  Eq.trans (congrArg (fun x => f x b) ha) (congrArg (f a') hb)

private theorem congrArg3 (f : α → β → γ → δ)
    {a a' : α} {b b' : β} {c c' : γ} (ha : a = a') (hb : b = b')
    (hc : c = c') : f a b c = f a' b' c' :=
  Eq.trans (congrArg (fun x => f x b c) ha) (congrArg2 (f a') hb hc)

/-- Pointwise composition avoids requiring equality of renaming functions. -/
theorem rename_composition (t : Term n) (ρ : Renaming n m)
    (τ : Renaming m k) (κ : Renaming n k) (h : ∀ i, τ (ρ i) = κ i) :
    rename τ (rename ρ t) = rename κ t :=
  match t with
  | .var i => congrArg Term.var (h i)
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .cmp op a b => congrArg2 (Term.cmp op)
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .cond c a b => congrArg3 Term.cond (rename_composition c ρ τ κ h)
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .pair a b => congrArg2 Term.pair
      (rename_composition a ρ τ κ h) (rename_composition b ρ τ κ h)
  | .fst a => congrArg Term.fst (rename_composition a ρ τ κ h)
  | .snd a => congrArg Term.snd (rename_composition a ρ τ κ h)
  | .value a => congrArg Term.value (rename_composition a ρ τ κ h)
  | .dfst a => congrArg Term.dfst (rename_composition a ρ τ κ h)
  | .inl b a => congrArg (Term.inl b) (rename_composition a ρ τ κ h)
  | .inr a b => congrArg (Term.inr a) (rename_composition b ρ τ κ h)
  | .case r s a b => congrArg3 (Term.case r) (rename_composition s ρ τ κ h)
      (rename_composition a (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))
      (rename_composition b (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))
  | .letIn a v body => congrArg2 (Term.letIn a) (rename_composition v ρ τ κ h)
      (rename_composition body (liftRen ρ) (liftRen τ) (liftRen κ)
        (Fin.cases rfl (fun i => congrArg Fin.succ (h i))))
  | .ann t a => congrArg (fun v => Term.ann v a) (rename_composition t ρ τ κ h)

theorem rename_comp (t : Term n) (ρ : Renaming n m) (τ : Renaming m k) :
    rename τ (rename ρ t) = rename (fun i => τ (ρ i)) t :=
  rename_composition t ρ τ (fun i => τ (ρ i)) (fun (_i) => rfl)

theorem rename_congr (t : Term n) (ρ τ : Renaming n m) (h : ∀ i, ρ i = τ i) :
    rename ρ t = rename τ t :=
  Eq.trans (rename_id (rename ρ t)).symm (rename_composition t ρ id τ h)

theorem rename_weaken (t : Term n) (ρ : Renaming n m) :
    rename (liftRen ρ) (rename Fin.succ t) = rename Fin.succ (rename ρ t) :=
  Eq.trans (rename_comp t Fin.succ (liftRen ρ)) (rename_comp t ρ Fin.succ).symm

/-- Substituting after renaming selects the replacement for the renamed index. -/
theorem subst_renaming (t : Term n) (ρ : Renaming n m)
    (σ : Substitution m k) (θ : Substitution n k) (h : ∀ i, σ (ρ i) = θ i) :
    subst σ (rename ρ t) = subst θ t :=
  match t with
  | .var i => h i
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .cmp op a b => congrArg2 (Term.cmp op)
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .cond c a b => congrArg3 Term.cond (subst_renaming c ρ σ θ h)
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .pair a b => congrArg2 Term.pair
      (subst_renaming a ρ σ θ h) (subst_renaming b ρ σ θ h)
  | .fst a => congrArg Term.fst (subst_renaming a ρ σ θ h)
  | .snd a => congrArg Term.snd (subst_renaming a ρ σ θ h)
  | .value a => congrArg Term.value (subst_renaming a ρ σ θ h)
  | .dfst a => congrArg Term.dfst (subst_renaming a ρ σ θ h)
  | .inl b a => congrArg (Term.inl b) (subst_renaming a ρ σ θ h)
  | .inr a b => congrArg (Term.inr a) (subst_renaming b ρ σ θ h)
  | .case r s a b => congrArg3 (Term.case r) (subst_renaming s ρ σ θ h)
      (subst_renaming a (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (rename Fin.succ) (h i))))
      (subst_renaming b (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (rename Fin.succ) (h i))))
  | .letIn a v body => congrArg2 (Term.letIn a) (subst_renaming v ρ σ θ h)
      (subst_renaming body (liftRen ρ) (liftSub σ) (liftSub θ)
        (Fin.cases rfl (fun i => congrArg (rename Fin.succ) (h i))))
  | .ann t a => congrArg (fun v => Term.ann v a) (subst_renaming t ρ σ θ h)

theorem subst_rename (t : Term n) (ρ : Renaming n m) (σ : Substitution m k) :
    subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t :=
  subst_renaming t ρ σ (fun i => σ (ρ i)) (fun (_i) => rfl)

theorem subst_congr (t : Term n) (σ τ : Substitution n m) (h : ∀ i, σ i = τ i) :
    subst σ t = subst τ t :=
  Eq.trans (congrArg (subst σ) (rename_id t)).symm (subst_renaming t id σ τ h)

private theorem liftSub_renaming (σ : Substitution n m) (ρ : Renaming m k)
    (θ : Substitution n k) (h : ∀ i, rename ρ (σ i) = θ i) :
    ∀ i, rename (liftRen ρ) (liftSub σ i) = liftSub θ i :=
  Fin.cases rfl (fun i => Eq.trans (rename_weaken (σ i) ρ)
    (congrArg (rename Fin.succ) (h i)))

/-- Renaming a substitution also renames every open replacement. -/
theorem rename_substitution (t : Term n) (σ : Substitution n m)
    (ρ : Renaming m k) (θ : Substitution n k) (h : ∀ i, rename ρ (σ i) = θ i) :
    rename ρ (subst σ t) = subst θ t :=
  match t with
  | .var i => h i
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .cmp op a b => congrArg2 (Term.cmp op)
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .cond c a b => congrArg3 Term.cond (rename_substitution c σ ρ θ h)
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .pair a b => congrArg2 Term.pair
      (rename_substitution a σ ρ θ h) (rename_substitution b σ ρ θ h)
  | .fst a => congrArg Term.fst (rename_substitution a σ ρ θ h)
  | .snd a => congrArg Term.snd (rename_substitution a σ ρ θ h)
  | .value a => congrArg Term.value (rename_substitution a σ ρ θ h)
  | .dfst a => congrArg Term.dfst (rename_substitution a σ ρ θ h)
  | .inl b a => congrArg (Term.inl b) (rename_substitution a σ ρ θ h)
  | .inr a b => congrArg (Term.inr a) (rename_substitution b σ ρ θ h)
  | .case r s a b => congrArg3 (Term.case r) (rename_substitution s σ ρ θ h)
      (rename_substitution a (liftSub σ) (liftRen ρ) (liftSub θ)
        (liftSub_renaming σ ρ θ h))
      (rename_substitution b (liftSub σ) (liftRen ρ) (liftSub θ)
        (liftSub_renaming σ ρ θ h))
  | .letIn a v body => congrArg2 (Term.letIn a) (rename_substitution v σ ρ θ h)
      (rename_substitution body (liftSub σ) (liftRen ρ) (liftSub θ)
        (liftSub_renaming σ ρ θ h))
  | .ann t a => congrArg (fun v => Term.ann v a) (rename_substitution t σ ρ θ h)

theorem rename_subst (t : Term n) (σ : Substitution n m) (ρ : Renaming m k) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t :=
  rename_substitution t σ ρ (fun i => rename ρ (σ i)) (fun (_i) => rfl)

theorem subst_weaken (t : Term n) (σ : Substitution n m) :
    subst (liftSub σ) (rename Fin.succ t) = rename Fin.succ (subst σ t) :=
  Eq.trans (subst_rename t Fin.succ (liftSub σ)) (rename_subst t σ Fin.succ).symm

private theorem liftSub_composition (σ : Substitution n m) (τ : Substitution m k)
    (θ : Substitution n k) (h : ∀ i, subst τ (σ i) = θ i) :
    ∀ i, subst (liftSub τ) (liftSub σ i) = liftSub θ i :=
  Fin.cases rfl (fun i => Eq.trans (subst_weaken (σ i) τ)
    (congrArg (rename Fin.succ) (h i)))

/-- Simultaneous substitutions compose even below nested lets and case binders. -/
theorem subst_composition (t : Term n) (σ : Substitution n m)
    (τ : Substitution m k) (θ : Substitution n k) (h : ∀ i, subst τ (σ i) = θ i) :
    subst τ (subst σ t) = subst θ t :=
  match t with
  | .var i => h i
  | .uint v => congrArg Term.uint (Eq.refl v)
  | .boolean v => congrArg Term.boolean (Eq.refl v)
  | .add a b => congrArg2 Term.add
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .cmp op a b => congrArg2 (Term.cmp op)
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .cond c a b => congrArg3 Term.cond (subst_composition c σ τ θ h)
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .pair a b => congrArg2 Term.pair
      (subst_composition a σ τ θ h) (subst_composition b σ τ θ h)
  | .fst a => congrArg Term.fst (subst_composition a σ τ θ h)
  | .snd a => congrArg Term.snd (subst_composition a σ τ θ h)
  | .value a => congrArg Term.value (subst_composition a σ τ θ h)
  | .dfst a => congrArg Term.dfst (subst_composition a σ τ θ h)
  | .inl b a => congrArg (Term.inl b) (subst_composition a σ τ θ h)
  | .inr a b => congrArg (Term.inr a) (subst_composition b σ τ θ h)
  | .case r s a b => congrArg3 (Term.case r) (subst_composition s σ τ θ h)
      (subst_composition a (liftSub σ) (liftSub τ) (liftSub θ)
        (liftSub_composition σ τ θ h))
      (subst_composition b (liftSub σ) (liftSub τ) (liftSub θ)
        (liftSub_composition σ τ θ h))
  | .letIn a v body => congrArg2 (Term.letIn a) (subst_composition v σ τ θ h)
      (subst_composition body (liftSub σ) (liftSub τ) (liftSub θ)
        (liftSub_composition σ τ θ h))
  | .ann t a => congrArg (fun v => Term.ann v a) (subst_composition t σ τ θ h)

theorem subst_comp (t : Term n) (σ : Substitution n m) (τ : Substitution m k) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t :=
  subst_composition t σ τ (fun i => subst τ (σ i)) (fun (_i) => rfl)

/-- Removing an unused newest binder cancels weakening. -/
theorem instantiate_weaken (t : Term n) (a : Term n) :
    instantiate (rename Fin.succ t) a = t :=
  Eq.trans (subst_renaming t Fin.succ (single a) Term.var (fun (_i) => rfl)) (subst_id t)

/-- Substitution commutes with binder removal when the body uses its lifted map. -/
theorem subst_instantiate (body : Term (n + 1)) (a : Term n)
    (σ : Substitution n m) :
    subst σ (instantiate body a) =
      instantiate (subst (liftSub σ) body) (subst σ a) :=
  Eq.trans (subst_comp body (single a) σ)
    (subst_composition body (liftSub σ) (single (subst σ a))
      (fun i => subst σ (single a i))
      (Fin.cases rfl (fun i => instantiate_weaken (σ i) (subst σ a)))).symm

end AgentWasm.Finite
