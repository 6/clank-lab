import Mathlib

/-!
# Lemma 9 (two-point bound) and the bracket it produces

For a nonempty family of `N` integers with mean `M`, let `α` be the largest
value `≤ M` and `β` the smallest value `≥ M`. No value lies strictly between
them, so `Σ (x - α)(x - β) ≥ 0`, i.e. `Σ x² ≥ N (M*M + (M - α)(β - M))`.
-/

namespace CubelikeSC

lemma bracket {ι : Type*} (I : Finset ι) (f : ι → ℤ) (N : ℕ) (hN : I.card = N) (hpos : 0 < N)
    (M : ℚ) (hM : (∑ i ∈ I, (f i : ℚ)) = N * M) :
    ∃ α β : ℤ, (∃ i ∈ I, f i = α) ∧ (∃ i ∈ I, f i = β) ∧ (α : ℚ) ≤ M ∧ M ≤ β ∧
      (N : ℚ) * (M ^ 2 + (M - α) * (β - M)) ≤ ∑ i ∈ I, ((f i : ℚ) ^ 2) := by
  have hI : I.Nonempty := Finset.card_pos.1 (hN ▸ hpos)
  set lo := (I.filter fun i => (f i : ℚ) ≤ M).image f
  set hi := (I.filter fun i => M ≤ (f i : ℚ)).image f
  have hlo : lo.Nonempty := by
    by_contra hne
    simp only [lo, Finset.image_nonempty, Finset.not_nonempty_iff_eq_empty,
      Finset.filter_eq_empty_iff, not_le] at hne
    have := Finset.sum_lt_sum_of_nonempty hI hne
    simp [hN] at this; linarith
  have hhi : hi.Nonempty := by
    by_contra hne
    simp only [hi, Finset.image_nonempty, Finset.not_nonempty_iff_eq_empty,
      Finset.filter_eq_empty_iff, not_le] at hne
    have := Finset.sum_lt_sum_of_nonempty hI hne
    simp [hN] at this; linarith
  obtain ⟨ia, ia', ea⟩ := Finset.mem_image.1 (lo.max'_mem hlo)
  obtain ⟨ib, ib', eb⟩ := Finset.mem_image.1 (hi.min'_mem hhi)
  have hαM : ((lo.max' hlo : ℤ) : ℚ) ≤ M := by rw [← ea]; exact (Finset.mem_filter.1 ia').2
  have hMβ : M ≤ ((hi.min' hhi : ℤ) : ℚ) := by rw [← eb]; exact (Finset.mem_filter.1 ib').2
  refine ⟨lo.max' hlo, hi.min' hhi, ⟨ia, (Finset.mem_filter.1 ia').1, ea⟩,
    ⟨ib, (Finset.mem_filter.1 ib').1, eb⟩, hαM, hMβ, ?_⟩
  · set α := lo.max' hlo
    set β := hi.min' hhi
    have hterm : ∀ i ∈ I, 0 ≤ ((f i : ℚ) - α) * ((f i : ℚ) - β) := by
      intro i hiI
      by_cases hle : (f i : ℚ) ≤ M
      · have : f i ≤ α := lo.le_max' _ (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hiI, hle⟩, rfl⟩)
        have : (f i : ℚ) ≤ α := by exact_mod_cast this
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hge : M ≤ (f i : ℚ) := le_of_lt (not_le.1 hle)
        have : β ≤ f i := hi.min'_le _ (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hiI, hge⟩, rfl⟩)
        have : (β : ℚ) ≤ f i := by exact_mod_cast this
        exact mul_nonneg (by linarith) (by linarith)
    have hsum := Finset.sum_nonneg hterm
    have hexp : ∑ i ∈ I, ((f i : ℚ) - α) * ((f i : ℚ) - β) =
        ∑ i ∈ I, ((f i : ℚ) ^ 2) - (α + β) * ∑ i ∈ I, (f i : ℚ) + N * (α * β) := by
      rw [Finset.mul_sum]
      simp only [← Finset.sum_sub_distrib]
      rw [show (N : ℚ) * (α * β) = ∑ _i ∈ I, ((α : ℚ) * β) by simp [hN]]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hexp, hM] at hsum
    nlinarith

end CubelikeSC
