import CD13.HK
import CD13.Trace

/-! From dynamical observations to presented-monoid equality. -/
namespace CD13.AlgebraBridge

variable {V : Type u}

/-- Exactly the distinct disconnected pairs whose generators commute. -/
def Independent (E : V → V → Prop) (a b : V) : Prop :=
  a ≠ b ∧ ¬ E a b ∧ ¬ E b a

/-- Fixed algebraic separation endpoint. The observation hypotheses below
remain to be supplied by the dynamical model. -/
def SeparationEndpoint (E : V → V → Prop) [DecidableEq V]
    {O : Sort v} (observe : List V → O) : Prop :=
  (∀ u v, HK.Rel E u v → observe u = observe v) →
  (∀ u v, Reduction.RepeatProperty E u → Reduction.RepeatProperty E v →
    observe u.reverse = observe v.reverse →
    (∀ a, Trace.projection a a u = Trace.projection a a v) ∧
    (∀ a b, E a b → Trace.projection a b u = Trace.projection a b v)) →
  ∀ u v, observe u = observe v → HK.Rel E u v

 theorem independent_irrefl (E : V → V → Prop) (a : V) : ¬ Independent E a a := by
  intro h
  exact h.1 rfl

 theorem independent_symm (E : V → V → Prop) (a b : V)
    (h : Independent E a b) : Independent E b a :=
  ⟨Ne.symm h.1, h.2.2, h.2.1⟩

 theorem trace_to_hk (E : V → V → Prop) {u v : List V}
    (h : Trace.Equiv (Independent E) u v) : HK.Rel E u v := by
  induction h with
  | nil => exact .refl []
  | cons a h ih => exact .append (.refl [a]) ih
  | swap a b w h =>
      exact .append (.commute a b h.1 h.2.1 h.2.2) (.refl w)
  | trans h k ih ik => exact .trans ih ik

 theorem trace_reverse_to_hk (E : V → V → Prop) {u v : List V}
    (h : Trace.Equiv (Independent E) u v) : HK.Rel E u.reverse v.reverse := by
  induction h with
  | nil => exact .refl []
  | cons a h ih =>
      simpa using HK.Rel.append ih (HK.Rel.refl [a])
  | swap a b w h =>
      have hc := HK.Rel.commute b a (Ne.symm h.1) h.2.2 h.2.1
      simpa using HK.Rel.append (HK.Rel.refl w.reverse) hc
  | trans h k ih ik => exact .trans ih ik

 theorem projection_comm [DecidableEq V] (a b : V) (w : List V) :
    Trace.projection a b w = Trace.projection b a w := by
  simp [Trace.projection, or_comm]

 theorem dependent_projections [DecidableEq V] (E : V → V → Prop)
    (u v : List V)
    (single : ∀ a, Trace.projection a a u = Trace.projection a a v)
    (edge : ∀ a b, E a b → Trace.projection a b u = Trace.projection a b v) :
    ∀ a b, ¬ Independent E a b → Trace.projection a b u = Trace.projection a b v := by
  intro a b h
  by_cases hab : a = b
  · subst b
    exact single a
  · by_cases he : E a b
    · exact edge a b he
    · by_cases hf : E b a
      · simpa only [projection_comm a b] using edge b a hf
      · exact False.elim (h ⟨hab, he, hf⟩)

 theorem reconstruct_reverse [DecidableEq V] (E : V → V → Prop)
    (u v : List V)
    (single : ∀ a, Trace.projection a a u = Trace.projection a a v)
    (edge : ∀ a b, E a b → Trace.projection a b u = Trace.projection a b v) :
    HK.Rel E u.reverse v.reverse := by
  exact trace_reverse_to_hk E (Trace.reconstruct (Independent E)
    (independent_irrefl E) (independent_symm E) u v
    (dependent_projections E u v single edge))

 theorem word_separation [DecidableEq V] (E : V → V → Prop)
    {O : Sort v} (observe : List V → O)
    (respect : ∀ u v, HK.Rel E u v → observe u = observe v)
    (recover : ∀ u v, Reduction.RepeatProperty E u → Reduction.RepeatProperty E v →
      observe u.reverse = observe v.reverse →
      (∀ a, Trace.projection a a u = Trace.projection a a v) ∧
      (∀ a b, E a b → Trace.projection a b u = Trace.projection a b v))
    (u v : List V) (heq : observe u = observe v) : HK.Rel E u v := by
  obtain ⟨u', hu, hru, _⟩ := HK.reduced_representative E u
  obtain ⟨v', hv, hrv, _⟩ := HK.reduced_representative E v
  have heq' : observe u' = observe v' :=
    (respect u u' hu).symm.trans (heq.trans (respect v v' hv))
  have hp := recover u'.reverse v'.reverse
    (Reduction.repeat_reverse E u' hru) (Reduction.repeat_reverse E v' hrv)
    (by simpa using heq')
  have hrel : HK.Rel E u' v' := by
    simpa using reconstruct_reverse E u'.reverse v'.reverse hp.1 hp.2
  exact .trans hu (.trans hrel (.symm hv))

 theorem separationEndpoint [DecidableEq V] (E : V → V → Prop)
    {O : Sort v} (observe : List V → O) : SeparationEndpoint E observe := by
  intro respect recover u v heq
  exact word_separation E observe respect recover u v heq

/-- One separating model identifies the intersection of all model kernels.
Admissibility and respect for HK must be proved by the calling model file. -/
 theorem kernel_intersection (E : V → V → Prop) {M : Type v}
    {O : M → Sort w} (observe : (m : M) → List V → O m)
    (respect : ∀ m u v, HK.Rel E u v → observe m u = observe m v)
    (m₀ : M) (sep : ∀ u v, observe m₀ u = observe m₀ v → HK.Rel E u v)
    (u v : List V) :
    HK.Rel E u v ↔ ∀ m, observe m u = observe m v := by
  constructor
  · intro h m
    exact respect m u v h
  · intro h
    exact sep u v (h m₀)

end CD13.AlgebraBridge
