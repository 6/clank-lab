import P16c.MatrixDefs

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo

lemma nonzero_of_order_ge_three {l : K} {s : ℕ} (hl : orderOf l = s) (hs : 3 ≤ s) :
    l ≠ 0 := by
  intro h
  subst l
  simp only [orderOf_zero] at hl
  omega

lemma sq_ne_one_of_order_ge_three {l : K} {s : ℕ} (hl : orderOf l = s) (hs : 3 ≤ s) :
    l ^ 2 ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hl] at hd
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma traceParam_ne_zero {l : K} (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) :
    traceParam l ≠ 0 := by
  intro h
  apply hl2
  have hx : l * traceParam l = 0 := by rw [h, mul_zero]
  have hy : l ^ 2 + 1 = 0 := by
    simpa [traceParam, mul_add, pow_two, hl] using hx
  exact eq_of_sub_eq_zero (by simpa using hy)

lemma traceParam_eq_iff {l m : K} (hl : l ≠ 0) (hm : m ≠ 0) :
    traceParam l = traceParam m ↔ m = l ∨ m = l⁻¹ := by
  constructor
  · intro h
    have hp : (m - l) * (m - l⁻¹) = 0 := by
      have htrace : l + l⁻¹ = m + m⁻¹ := h
      calc
        (m - l) * (m - l⁻¹) = m * ((m + m⁻¹) - (l + l⁻¹)) := by
          field_simp
          <;> ring
        _ = 0 := by rw [htrace]; simp
    simpa only [sub_eq_zero] using mul_eq_zero.mp hp
  · rintro (rfl | rfl) <;> simp [traceParam, add_comm]

/-- L1: all denominators and the three required parameters are nonzero. -/
theorem parameters (s u : ℕ) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    traceParam l ≠ 0 ∧ traceParam m ≠ 0 ∧
      aParam l m ≠ 0 ∧ bParam l m ≠ 0 ∧ aParam l m + bParam l m = traceParam l := by
  have hl0 := nonzero_of_order_ge_three hl hs3
  have hm0 := nonzero_of_order_ge_three hm hu3
  have hσ := traceParam_ne_zero hl0 (sq_ne_one_of_order_ge_three hl hs3)
  have hτ := traceParam_ne_zero hm0 (sq_ne_one_of_order_ge_three hm hu3)
  have hne : traceParam l ≠ traceParam m := by
    intro h
    rcases (traceParam_eq_iff hl0 hm0).mp h with h | h
    · subst m; exact hsu (hl.symm.trans hm)
    · have hi : orderOf l⁻¹ = orderOf l := by
        rw [orderOf_eq_orderOf_iff]
        intro n
        simp
      rw [h, hi] at hm
      exact hsu (hl.symm.trans hm)
  refine ⟨hσ, hτ, div_ne_zero (pow_ne_zero _ hσ) hτ, ?_, ?_⟩
  · intro hb
    have hid : bParam l m * traceParam m = traceParam l * (traceParam m + traceParam l) := by
      dsimp [bParam, aParam]
      field_simp
      <;> ring
    rw [hb, zero_mul] at hid
    rcases mul_eq_zero.mp hid.symm with h | h
    · exact hσ h
    · apply hne
      exact (eq_of_sub_eq_zero (by simpa [add_comm] using h)).symm
  · simp [bParam, add_comm, add_left_comm]
end P16c
