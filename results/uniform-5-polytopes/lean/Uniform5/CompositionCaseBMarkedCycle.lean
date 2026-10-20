import Uniform5.CompositionCaseBCellSeparation

/-! A strict angle budget allows at most one antiprism ray. -/
noncomputable section
namespace Uniform5.Composition
open scoped BigOperators

/-- A marked ray costs a right angle on each adjacent side.  No side has two
marked ends, so those costs add without overlap. -/
theorem marked_cycle_count_le_one {k : ℕ} (p : Fin k → Prop) [DecidablePred p]
    (a : Fin k → ℝ) (hlo : ∀ i, 0 ≤ a i)
    (hadj : ∀ i, ¬ (p i ∧ p (finRotate k i)))
    (hright : ∀ i, p i ∨ p (finRotate k i) → a i = Real.pi / 2)
    (hsum : ∑ i, a i < 2 * Real.pi) :
    (Finset.univ.filter p).card ≤ 1 := by
  let b : Fin k → ℝ := fun i => if p i then 1 else 0
  have hb : ∑ i, b i = ((Finset.univ.filter p).card : ℝ) := by
    simp [b, Finset.sum_boole]
  have hrot : ∑ i, b (finRotate k i) = ∑ i, b i := Equiv.sum_comp (finRotate k) b
  have hp (i : Fin k) : Real.pi / 2 * (b i + b (finRotate k i)) ≤ a i := by
    by_cases hi : p i <;> by_cases hj : p (finRotate k i)
    · exact (hadj i ⟨hi, hj⟩).elim
    · rw [hright i (Or.inl hi)]
      simp [b, hi, hj]
    · rw [hright i (Or.inr hj)]
      simp [b, hi, hj]
    · simpa [b, hi, hj] using hlo i
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hrot, hb] at hh
  by_contra h
  have hc : (2 : ℝ) ≤ (Finset.univ.filter p).card := by
    exact_mod_cast (show 2 ≤ (Finset.univ.filter p).card by omega)
  nlinarith [Real.pi_pos]

/-- With one marked ray, the remaining angle budget permits at most four rays. -/
theorem marked_cycle_length_le_four {k : ℕ} (p : Fin k → Prop) [DecidablePred p]
    (a : Fin k → ℝ) (hlo : ∀ i, Real.pi / 3 ≤ a i)
    (hadj : ∀ i, ¬ (p i ∧ p (finRotate k i)))
    (hright : ∀ i, p i ∨ p (finRotate k i) → a i = Real.pi / 2)
    (hex : ∃ i, p i) (hsum : ∑ i, a i < 2 * Real.pi) : k ≤ 4 := by
  let b : Fin k → ℝ := fun i => if p i then 1 else 0
  have hb : ∑ i, b i = ((Finset.univ.filter p).card : ℝ) := by
    simp [b, Finset.sum_boole]
  have hrot : ∑ i, b (finRotate k i) = ∑ i, b i := Equiv.sum_comp (finRotate k) b
  have hp (i : Fin k) : Real.pi / 3 + Real.pi / 6 * (b i + b (finRotate k i)) ≤ a i := by
    by_cases hi : p i <;> by_cases hj : p (finRotate k i)
    · exact (hadj i ⟨hi, hj⟩).elim
    · rw [hright i (Or.inl hi)]
      simp [b, hi, hj]
      linarith
    · rw [hright i (Or.inr hj)]
      simp [b, hi, hj]
      linarith
    · simpa [b, hi, hj] using hlo i
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hrot, hb] at hh
  have hc : (1 : ℝ) ≤ (Finset.univ.filter p).card := by
    have hpos : 0 < (Finset.univ.filter p).card := Finset.card_pos.mpr (by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
    exact_mod_cast (Nat.succ_le_of_lt hpos)
  by_contra h
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast (show 5 ≤ k by omega)
  nlinarith [Real.pi_pos]

end Uniform5.Composition
