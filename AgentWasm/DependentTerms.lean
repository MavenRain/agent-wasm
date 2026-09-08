import AgentWasm.DependentContexts
import AgentWasm.ErasedContexts

namespace AgentWasm.Dependent

open Finite
open Finite.Phased

/-- Finite indices remain separate from dependent values. In particular,
    a refinement payload projection cannot yet occur inside an index. -/
inductive Term : Nat → Type where
  | var : Fin n → Term n
  | finite : Finite.Term n → Term n
  | refl : Finite.Term n → Term n
  | pair : Term n → Term n → Term n
  | fst : Term n → Term n
  | snd : Term n → Term n
  | inl : Indexed.Ty n → Term n → Term n
  | inr : Indexed.Ty n → Term n → Term n
  | case : Indexed.Ty n → Term n → Term (n + 1) → Term (n + 1) → Term n
  | cond : Finite.Term n → Term n → Term n → Term n
  | ifProof : Indexed.Ty n → Finite.Term n → Term (n + 1) →
      Term (n + 1) → Term n
  | pack : Finite.Ty → Finite.Term (n + 1) → Finite.Term (n + 1) →
      Finite.Term n → Term n → Term n
  | value : Term n → Term n
  | dpair : Finite.Ty → Indexed.Ty (n + 1) → Finite.Term n → Term n → Term n
  | dfst : Term n → Term n
  | letIn : Relevance → Indexed.Ty n → Term n → Term (n + 1) → Term n
  | ann : Term n → Indexed.Ty n → Term n
  deriving Repr

def rename (ρ : Renaming n m) : Term n → Term m
  | .var i => .var (ρ i)
  | .finite t => .finite (Finite.rename ρ t)
  | .refl t => .refl (Finite.rename ρ t)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst t => .fst (rename ρ t)
  | .snd t => .snd (rename ρ t)
  | .inl b t => .inl (Indexed.rename ρ b) (rename ρ t)
  | .inr a t => .inr (Indexed.rename ρ a) (rename ρ t)
  | .case r s a b => .case (Indexed.rename ρ r) (rename ρ s)
      (rename (liftRen ρ) a) (rename (liftRen ρ) b)
  | .cond c a b => .cond (Finite.rename ρ c) (rename ρ a) (rename ρ b)
  | .ifProof r c a b => .ifProof (Indexed.rename ρ r) (Finite.rename ρ c)
      (rename (liftRen ρ) a) (rename (liftRen ρ) b)
  | .pack a l r v h => .pack a (Finite.rename (liftRen ρ) l)
      (Finite.rename (liftRen ρ) r) (Finite.rename ρ v) (rename ρ h)
  | .value t => .value (rename ρ t)
  | .dpair a b v t => .dpair a (Indexed.rename (liftRen ρ) b)
      (Finite.rename ρ v) (rename ρ t)
  | .dfst t => .dfst (rename ρ t)
  | .letIn r a v b => .letIn r (Indexed.rename ρ a) (rename ρ v)
      (rename (liftRen ρ) b)
  | .ann t a => .ann (rename ρ t) (Indexed.rename ρ a)

private theorem congrArg2 (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' :=
  Eq.trans (congrArg (fun x => f x b) ha) (congrArg (f a') hb)

private theorem congrArg3 (f : α → β → γ → δ)
    {a a' : α} {b b' : β} {c c' : γ}
    (ha : a = a') (hb : b = b') (hc : c = c') : f a b c = f a' b' c' :=
  Eq.trans (congrArg (fun x => f x b c) ha) (congrArg2 (f a') hb hc)

private theorem congrArg4 (f : α → β → γ → δ → ε)
    {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    f a b c d = f a' b' c' d' :=
  Eq.trans (congrArg (fun x => f x b c d) ha) (congrArg3 (f a') hb hc hd)

theorem rename_identity (t : Term n) (ρ : Renaming n n) (h : ∀ i, ρ i = i) :
    rename ρ t = t :=
  match t with
  | .var i => congrArg Term.var (h i)
  | .finite t => congrArg Term.finite (Finite.rename_identity t ρ h)
  | .refl t => congrArg Term.refl (Finite.rename_identity t ρ h)
  | .pair a b => congrArg2 Term.pair
      (rename_identity a ρ h) (rename_identity b ρ h)
  | .fst t => congrArg Term.fst (rename_identity t ρ h)
  | .snd t => congrArg Term.snd (rename_identity t ρ h)
  | .inl b t => congrArg2 Term.inl
      (Indexed.rename_identity b ρ h) (rename_identity t ρ h)
  | .inr a t => congrArg2 Term.inr
      (Indexed.rename_identity a ρ h) (rename_identity t ρ h)
  | .case r s a b => congrArg4 Term.case
      (Indexed.rename_identity r ρ h) (rename_identity s ρ h)
      (rename_identity a (liftRen ρ) (liftRen_identity h))
      (rename_identity b (liftRen ρ) (liftRen_identity h))
  | .cond c a b => congrArg3 Term.cond (Finite.rename_identity c ρ h)
      (rename_identity a ρ h) (rename_identity b ρ h)
  | .ifProof r c a b => congrArg4 Term.ifProof
      (Indexed.rename_identity r ρ h) (Finite.rename_identity c ρ h)
      (rename_identity a (liftRen ρ) (liftRen_identity h))
      (rename_identity b (liftRen ρ) (liftRen_identity h))
  | .pack a l r v hh => Eq.trans
      (congrArg (fun x => Term.pack a x (Finite.rename (liftRen ρ) r)
        (Finite.rename ρ v) (rename ρ hh))
        (Finite.rename_identity l (liftRen ρ) (liftRen_identity h)))
      (congrArg3 (Term.pack a l)
        (Finite.rename_identity r (liftRen ρ) (liftRen_identity h))
        (Finite.rename_identity v ρ h) (rename_identity hh ρ h))
  | .value t => congrArg Term.value (rename_identity t ρ h)
  | .dpair a b v t => congrArg3 (Term.dpair a)
      (Indexed.rename_identity b (liftRen ρ) (liftRen_identity h))
      (Finite.rename_identity v ρ h) (rename_identity t ρ h)
  | .dfst t => congrArg Term.dfst (rename_identity t ρ h)
  | .letIn r a v b => congrArg3 (Term.letIn r)
      (Indexed.rename_identity a ρ h) (rename_identity v ρ h)
      (rename_identity b (liftRen ρ) (liftRen_identity h))
  | .ann t a => congrArg2 Term.ann
      (rename_identity t ρ h) (Indexed.rename_identity a ρ h)

theorem rename_id (t : Term n) : rename id t = t :=
  rename_identity t id (fun (_i) => rfl)

def ArgumentPhase (p : Phase) : Relevance → Phase
  | .run => p
  | .erase => .ghost

/-- No exposed equality evidence can be returned by an Execute term. -/
def RuntimeType : Phase → Indexed.Ty n → Prop
  | .execute, a => Indexed.BranchType a
  | .ghost, (_a) => True

theorem runtimeType_rename (p : Phase) (a : Indexed.Ty n)
    (ρ : Renaming n m) : RuntimeType p (Indexed.rename ρ a) = RuntimeType p a :=
  match p with
  | .execute => Indexed.branch_rename a ρ
  | .ghost => rfl

/-- Reify a Boolean condition as the finite index used by branch evidence. -/
def indicator (c : Finite.Term n) : Finite.Term n :=
  .cond c (.uint 1) (.uint 0)

/-- A proof branch receives this declaration before its binder is added. -/
def branchEvidence (c : Finite.Term n) (outcome : Fin (2 ^ 32)) :
    Indexed.Ty n :=
  .eq (indicator c) (.uint outcome)

theorem indicator_rename (c : Finite.Term n) (ρ : Renaming n m) :
    Finite.rename ρ (indicator c) = indicator (Finite.rename ρ c) := rfl

theorem branchEvidence_rename (c : Finite.Term n) (outcome : Fin (2 ^ 32))
    (ρ : Renaming n m) :
    Indexed.rename ρ (branchEvidence c outcome) =
      branchEvidence (Finite.rename ρ c) outcome := rfl

theorem indicator_hasType {Γ : Context n} {c : Finite.Term n}
    (hc : IndexHasType Γ c .bool) : IndexHasType Γ (indicator c) .u32 :=
  .cond hc .uint .uint

theorem branchEvidence_wellFormed {Γ : Context n} {c : Finite.Term n}
    (hc : IndexHasType Γ c .bool) (outcome : Fin (2 ^ 32)) :
    WellFormed Γ (branchEvidence c outcome) :=
  .eq (indicator_hasType hc) .uint

/-- Exact schema equality is used here; conversion is a later obligation.
    Let and branch results are outer schemas, so new binders cannot escape. -/
inductive HasType : Phase → Context n → Quantities n →
    Term n → Indexed.Ty n → Prop where
  | var : WellFormed Γ (lookup Γ i) → Accessible p (q i) →
      RuntimeType p (lookup Γ i) → HasType p Γ q (.var i) (lookup Γ i)
  | finite : IndexHasType Γ t a → Allowed p q t →
      HasType p Γ q (.finite t) (.base a)
  | refl : IndexHasType Γ t .u32 → HasType .ghost Γ q (.refl t) (.eq t t)
  | pair : HasType p Γ q a x → HasType p Γ q b y →
      HasType p Γ q (.pair a b) (.product x y)
  | fst : HasType p Γ q t (.product a b) → HasType p Γ q (.fst t) a
  | snd : HasType p Γ q t (.product a b) → HasType p Γ q (.snd t) b
  | inl : WellFormed Γ b → Indexed.BranchType a → Indexed.BranchType b →
      HasType p Γ q t a → HasType p Γ q (.inl b t) (.sum a b)
  | inr : WellFormed Γ a → Indexed.BranchType a → Indexed.BranchType b →
      HasType p Γ q t b → HasType p Γ q (.inr a t) (.sum a b)
  | case : WellFormed Γ result → Indexed.BranchType result →
      HasType p Γ q s (.sum a b) →
      HasType p (.snoc Γ a) (extendWith q .run) l
        (Indexed.rename Fin.succ result) →
      HasType p (.snoc Γ b) (extendWith q .run) r
        (Indexed.rename Fin.succ result) →
      HasType p Γ q (.case result s l r) result
  | cond : IndexHasType Γ c .bool → Allowed p q c → Indexed.BranchType a →
      HasType p Γ q l a → HasType p Γ q r a →
      HasType p Γ q (.cond c l r) a
  | ifProof : WellFormed Γ result → Indexed.BranchType result →
      IndexHasType Γ c .bool → Allowed p q c →
      HasType p (.snoc Γ (branchEvidence c 1)) (extendWith q .erase) l
        (Indexed.rename Fin.succ result) →
      HasType p (.snoc Γ (branchEvidence c 0)) (extendWith q .erase) r
        (Indexed.rename Fin.succ result) →
      HasType p Γ q (.ifProof result c l r) result
  | pack : WellFormed Γ (.refine a l r) → IndexHasType Γ v a →
      Allowed p q v → HasType .ghost Γ q h
        (.eq (Finite.instantiate l v) (Finite.instantiate r v)) →
      HasType p Γ q (.pack a l r v h) (.refine a l r)
  | value : HasType p Γ q t (.refine a l r) →
      HasType p Γ q (.value t) (.base a)
  | dpair : WellFormed Γ (.sigma a b) → IndexHasType Γ v a →
      Allowed p q v → HasType p Γ q t (Indexed.instantiate b v) →
      HasType p Γ q (.dpair a b v t) (.sigma a b)
  | dfst : HasType p Γ q t (.sigma a b) →
      HasType p Γ q (.dfst t) (.base a)
  | letIn : WellFormed Γ a → WellFormed Γ b →
      HasType (ArgumentPhase p r) Γ q v a →
      HasType p (.snoc Γ a) (extendWith q r) body (Indexed.rename Fin.succ b) →
      HasType p Γ q (.letIn r a v body) b
  | ann : HasType p Γ q t a → HasType p Γ q (.ann t a) a

theorem HasType.wellFormed {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Indexed.Ty n} (ht : HasType p Γ q t a) : WellFormed Γ a :=
  match ht with
  | .var ha (_hq) (_hr) => ha
  | .finite (_ht) (_hq) => .base
  | .refl ht => .eq ht ht
  | .pair ha hb => .product ha.wellFormed hb.wellFormed
  | .fst ht => match ht.wellFormed with | .product ha (_hb) => ha
  | .snd ht => match ht.wellFormed with | .product (_ha) hb => hb
  | .inl hb ba bb ht => .sum ba bb ht.wellFormed hb
  | .inr ha ba bb ht => .sum ba bb ha ht.wellFormed
  | .case ha (_ba) (_hs) (_hl) (_hr) => ha
  | .cond (_hc) (_hq) (_ba) hl (_hr) => hl.wellFormed
  | .ifProof ha (_ba) (_hc) (_hq) (_hl) (_hr) => ha
  | .pack ha (_hv) (_hq) (_hh) => ha
  | .value (_ht) => .base
  | .dpair ha (_hv) (_hq) (_ht) => ha
  | .dfst (_ht) => .base
  | .letIn (_ha) hb (_hv) (_hbody) => hb
  | .ann ht => ht.wellFormed

private theorem runtime_product_left {p : Phase} {a b : Indexed.Ty n}
    (h : RuntimeType p (.product a b)) : RuntimeType p a :=
  match p with
  | .execute => h.1
  | .ghost => True.intro

private theorem runtime_product_right {p : Phase} {a b : Indexed.Ty n}
    (h : RuntimeType p (.product a b)) : RuntimeType p b :=
  match p with
  | .execute => h.2
  | .ghost => True.intro

private theorem runtime_branch (p : Phase) {a : Indexed.Ty n}
    (h : Indexed.BranchType a) : RuntimeType p a :=
  match p with
  | .execute => h
  | .ghost => True.intro

theorem HasType.runtimeType {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Indexed.Ty n} (ht : HasType p Γ q t a) :
    RuntimeType p a :=
  match ht with
  | .var (_ha) (_hq) hr => hr
  | .finite (_ht) (_hq) => runtime_branch _ True.intro
  | .refl (_ht) => True.intro
  | .pair ha hb => match p with
      | .execute => And.intro ha.runtimeType hb.runtimeType
      | .ghost => True.intro
  | .fst ht => runtime_product_left ht.runtimeType
  | .snd ht => runtime_product_right ht.runtimeType
  | .inl (_hb) ba bb (_ht) | .inr (_ha) ba bb (_ht) =>
      runtime_branch _ ⟨ba, bb⟩
  | .case (_ha) ba (_hs) (_hl) (_hr) => runtime_branch _ ba
  | .cond (_hc) (_hq) ba (_hl) (_hr) => runtime_branch _ ba
  | .ifProof (_ha) ba (_hc) (_hq) (_hl) (_hr) => runtime_branch _ ba
  | .pack (_ha) (_hv) (_hq) (_hh) => runtime_branch _ True.intro
  | .value (_ht) | .dfst (_ht) => runtime_branch _ True.intro
  | .dpair ha (_hv) (_hq) (_ht) => match ha with
      | .sigma hb (_wb) => runtime_branch _ hb
  | .letIn (_ha) (_hb) (_hv) hbody =>
      Eq.mp (runtimeType_rename _ _ Fin.succ) hbody.runtimeType
  | .ann ht => ht.runtimeType

theorem execute_equality_rejected {Γ : Context n} {q : Quantities n}
    {t : Term n} {l r : Finite.Term n} :
    ¬ HasType .execute Γ q t (.eq l r) := fun ht => ht.runtimeType

theorem erased_var_rejected {Γ : Context n} {q : Quantities n}
    {i : Fin n} {a : Indexed.Ty n} (hi : q i = .erase) :
    ¬ HasType .execute Γ q (.var i) a :=
  fun ht => match ht with
    | .var (_ha) hq (_hr) => Eq.mp (congrArg (Accessible .execute) hi) hq

theorem index_rename_instantiate (body : Finite.Term (n + 1))
    (v : Finite.Term n) (ρ : Renaming n m) :
    Finite.rename ρ (Finite.instantiate body v) =
      Finite.instantiate (Finite.rename (liftRen ρ) body) (Finite.rename ρ v) :=
  Eq.trans (Finite.rename_subst body (single v) ρ)
    (Finite.subst_renaming body (liftRen ρ) (single (Finite.rename ρ v))
      (fun i => Finite.rename ρ (single v i))
      (Fin.cases rfl (fun (_i) => rfl))).symm

theorem schema_rename_instantiate (body : Indexed.Ty (n + 1))
    (v : Finite.Term n) (ρ : Renaming n m) :
    Indexed.rename ρ (Indexed.instantiate body v) =
      Indexed.instantiate (Indexed.rename (liftRen ρ) body)
        (Finite.rename ρ v) :=
  Eq.trans (Indexed.rename_subst body (single v) ρ)
    (Indexed.subst_renaming body (liftRen ρ) (single (Finite.rename ρ v))
      (fun i => Finite.rename ρ (single v i))
      (Fin.cases rfl (fun (_i) => rfl))).symm

/-- Relevance equality preserves access in both phases, including a Ghost
    subterm reached from Execute. -/
def QuantityRenamingPreserves (q : Quantities n) (r : Quantities m)
    (ρ : Renaming n m) : Prop := ∀ i, r (ρ i) = q i

theorem quantityRenaming_access {q : Quantities n} {r : Quantities m}
    {ρ : Renaming n m} (h : QuantityRenamingPreserves q r ρ) (p : Phase) :
    Phased.RenamingPreserves p q r ρ :=
  fun i hi => Eq.mpr (congrArg (Accessible p) (h i)) hi

theorem quantityRenaming_lift {q : Quantities n} {r : Quantities m}
    {ρ : Renaming n m} (h : QuantityRenamingPreserves q r ρ) (s : Relevance) :
    QuantityRenamingPreserves (extendWith q s) (extendWith r s) (liftRen ρ) :=
  Fin.cases rfl h

theorem HasType.rename {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Indexed.Ty n} (ht : HasType p Γ q t a)
    {Δ : Context m} {r : Quantities m} (ρ : Renaming n m)
    (hΓ : RenamingPreserves Γ Δ ρ) (hq : QuantityRenamingPreserves q r ρ) :
    HasType p Δ r (Dependent.rename ρ t) (Indexed.rename ρ a) :=
  match ht with
  | .var ha hv hr =>
      (hΓ _) ▸ HasType.var
        ((hΓ _).symm ▸ ha.rename ρ hΓ)
        (quantityRenaming_access hq _ _ hv)
        ((hΓ _).symm ▸ Eq.mpr (runtimeType_rename _ _ ρ) hr)
  | .finite ht hv => .finite (ht.rename ρ hΓ)
      (hv.rename ρ (quantityRenaming_access hq _))
  | .refl ht => .refl (ht.rename ρ hΓ)
  | .pair ha hb => .pair (ha.rename ρ hΓ hq) (hb.rename ρ hΓ hq)
  | .fst ht => .fst (ht.rename ρ hΓ hq)
  | .snd ht => .snd (ht.rename ρ hΓ hq)
  | .inl hb ba bb ht => .inl (hb.rename ρ hΓ)
      (Eq.mpr (Indexed.branch_rename _ ρ) ba)
      (Eq.mpr (Indexed.branch_rename _ ρ) bb) (ht.rename ρ hΓ hq)
  | .inr ha ba bb ht => .inr (ha.rename ρ hΓ)
      (Eq.mpr (Indexed.branch_rename _ ρ) ba)
      (Eq.mpr (Indexed.branch_rename _ ρ) bb) (ht.rename ρ hΓ hq)
  | .case ha ba hs hl hr => .case (ha.rename ρ hΓ)
      (Eq.mpr (Indexed.branch_rename _ ρ) ba) (hs.rename ρ hΓ hq)
      (rename_weaken _ ρ ▸ hl.rename (liftRen ρ)
        (liftRen_preserves hΓ _) (quantityRenaming_lift hq _))
      (rename_weaken _ ρ ▸ hr.rename (liftRen ρ)
        (liftRen_preserves hΓ _) (quantityRenaming_lift hq _))
  | .cond hc hv ba hl hr => .cond (hc.rename ρ hΓ)
      (hv.rename ρ (quantityRenaming_access hq _))
      (Eq.mpr (Indexed.branch_rename _ ρ) ba)
      (hl.rename ρ hΓ hq) (hr.rename ρ hΓ hq)
  | .ifProof ha ba hc hv hl hr => .ifProof (ha.rename ρ hΓ)
      (Eq.mpr (Indexed.branch_rename _ ρ) ba) (hc.rename ρ hΓ)
      (hv.rename ρ (quantityRenaming_access hq _))
      (rename_weaken _ ρ ▸ hl.rename (liftRen ρ)
        (liftRen_preserves hΓ _) (quantityRenaming_lift hq _))
      (rename_weaken _ ρ ▸ hr.rename (liftRen ρ)
        (liftRen_preserves hΓ _) (quantityRenaming_lift hq _))
  | .pack ha hv hqv hh => .pack (ha.rename ρ hΓ) (hv.rename ρ hΓ)
      (hqv.rename ρ (quantityRenaming_access hq _))
      (index_rename_instantiate _ _ ρ ▸
        index_rename_instantiate _ _ ρ ▸ hh.rename ρ hΓ hq)
  | .value ht => .value (ht.rename ρ hΓ hq)
  | .dpair ha hv hqv ht => .dpair (ha.rename ρ hΓ) (hv.rename ρ hΓ)
      (hqv.rename ρ (quantityRenaming_access hq _))
      (schema_rename_instantiate _ _ ρ ▸ ht.rename ρ hΓ hq)
  | .dfst ht => .dfst (ht.rename ρ hΓ hq)
  | .letIn ha hb hv hbody => .letIn (ha.rename ρ hΓ) (hb.rename ρ hΓ)
      (hv.rename ρ hΓ hq)
      (rename_weaken _ ρ ▸ hbody.rename (liftRen ρ)
        (liftRen_preserves hΓ _) (quantityRenaming_lift hq _))
  | .ann ht => .ann (ht.rename ρ hΓ hq)

theorem HasType.weaken {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Indexed.Ty n} (ht : HasType p Γ q t a)
    (b : Indexed.Ty n) (r : Relevance) :
    HasType p (.snoc Γ b) (extendWith q r)
      (Dependent.rename Fin.succ t) (Indexed.rename Fin.succ a) :=
  ht.rename Fin.succ (fun (_i) => rfl) (fun (_i) => rfl)

end AgentWasm.Dependent
