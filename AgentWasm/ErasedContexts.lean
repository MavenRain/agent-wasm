import AgentWasm.Phases

namespace AgentWasm.Finite.Phased

/-- Extend an external finite context with either binder relevance. -/
def extendWith (q : Quantities n) (r : Relevance) : Quantities (n + 1) :=
  Fin.cases r q

/-- A fresh slot of either relevance does not change access to older
variables. -/
theorem Allowed.weakenWith {p : Phase} {q : Quantities n} {t : Term n}
    (ht : Allowed p q t) (r : Relevance) :
    Allowed p (extendWith q r) (Finite.rename Fin.succ t) :=
  ht.rename Fin.succ (fun (_i) h => h)

theorem HasType.weakenWith {p : Phase} {Γ : Context n} {q : Quantities n}
    {t : Term n} {a : Ty} (ht : HasType p Γ q t a) (b : Ty) (r : Relevance) :
    HasType p (Finite.extend Γ b) (extendWith q r)
      (Finite.rename Fin.succ t) a :=
  ⟨ht.1.weaken b, ht.2.weakenWith r⟩

private theorem erased_replacement_allowed {q : Quantities n} {v : Term n}
    (p : Phase) (hv : Allowed .ghost q v) :
    Accessible p .erase → Allowed p q v :=
  match p with
  | .execute => False.elim
  | .ghost => fun (_h) => hv

/-- An erased context slot needs only a Ghost replacement in either phase. -/
theorem Allowed.instantiate_erased {p : Phase} {q : Quantities n}
    {body : Term (n + 1)} {v : Term n}
    (hb : Allowed p (extendWith q .erase) body)
    (hv : Allowed .ghost q v) : Allowed p q (Finite.instantiate body v) :=
  hb.subst (single v)
    (Fin.cases (erased_replacement_allowed p hv) (fun (_i) h => h))

/-- Remove an erased context binder while retaining the body's phase.
This is a context theorem; the finite syntax still has runtime lets only. -/
theorem HasType.instantiate_erased {p : Phase} {Γ : Context n}
    {q : Quantities n} {body : Term (n + 1)} {v : Term n} {a b : Ty}
    (hb : HasType p (Finite.extend Γ a) (extendWith q .erase) body b)
    (hv : HasType .ghost Γ q v a) :
    HasType p Γ q (Finite.instantiate body v) b :=
  ⟨hb.1.instantiate hv.1, hb.2.instantiate_erased hv.2⟩

end AgentWasm.Finite.Phased
