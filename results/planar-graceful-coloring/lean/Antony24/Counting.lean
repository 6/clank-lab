import Antony24.Basic

/-! Finite port-counting argument. -/
namespace Antony24

/-- The all-instance counting step. No connectivity, parity or size bound. -/
theorem no_two_three {V : Type*} [Finite V] (G : SimpleGraph V)
    (p : V → V → ℕ)
    (one : ∀ v, ∃! w, G.Adj v w ∧ p v w = 1)
    (three : ∀ v, ∃! w, G.Adj v w ∧ p v w = 3)
    (one_three : ∀ v w, G.Adj v w → p v w = 1 → p w v = 3) :
    ∀ v w, G.Adj v w → p v w = 3 → p w v = 1 := by
  classical
  let f : V → V := fun v => (one v).choose
  have hf (v : V) : G.Adj v (f v) ∧ p v (f v) = 1 := (one v).choose_spec.1
  have hi : Function.Injective f := by
    intro v w h
    have hv : G.Adj (f v) v ∧ p (f v) v = 3 :=
      ⟨(hf v).1.symm, one_three v (f v) (hf v).1 (hf v).2⟩
    have hw : G.Adj (f v) w ∧ p (f v) w = 3 := by
      rw [h]
      exact ⟨(hf w).1.symm, one_three w (f w) (hf w).1 (hf w).2⟩
    exact (three (f v)).unique hv hw
  have hs := (Finite.injective_iff_surjective).mp hi
  intro v w h hp
  obtain ⟨u, hu⟩ := hs v
  have qu : G.Adj v u ∧ p v u = 3 := by
    rw [← hu]
    exact ⟨(hf u).1.symm, one_three u (f u) (hf u).1 (hf u).2⟩
  have eq : u = w := (three v).unique qu ⟨h, hp⟩
  subst u
  simpa [hu] using (hf w).2

#print axioms no_two_three
end Antony24
