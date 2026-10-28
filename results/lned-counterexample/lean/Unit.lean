import Generic

namespace LNEDExtension
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R]

lemma diff_zero (c : R) : diff c 0 = 0 := by simp [diff, shift]

lemma shift_natDegree (c : R) (p : R[X]) : (shift c p).natDegree = p.natDegree := by
  rw [shift, natDegree_comp, natDegree_X_add_C, mul_one]

lemma shift_leadingCoeff (c : R) (p : R[X]) :
    (shift c p).leadingCoeff = p.leadingCoeff := by
  have hq : (X + C c).natDegree ≠ 0 := by rw [natDegree_X_add_C]; decide
  rw [shift, leadingCoeff_comp hq, leadingCoeff_X_add_C]
  simp

lemma diff_degree_lt (c : R) (p : R[X]) (hp : p ≠ 0) :
    (diff c p).degree < p.degree := by
  have hs : shift c p ≠ 0 := by
    intro hz
    have hl := congrArg Polynomial.leadingCoeff hz
    rw [shift_leadingCoeff, leadingCoeff_zero] at hl
    exact hp (leadingCoeff_eq_zero.mp hl)
  have hd : p.degree = (shift c p).degree := by
    rw [degree_eq_natDegree hp, degree_eq_natDegree hs, shift_natDegree]
  exact degree_sub_lt hd hp (shift_leadingCoeff c p).symm

lemma locally_nilpotent (c : R) (p : R[X]) :
    ∃ N : ℕ, 0 < N ∧ ((diff c)^[N]) p = 0 := by
  have aux : ∀ n : ℕ, ∀ p : R[X], p.natDegree = n →
      ∃ N : ℕ, 0 < N ∧ ((diff c)^[N]) p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hz : diff c p = 0
      · exact ⟨1, by omega, by simpa using hz⟩
      · have hp : p ≠ 0 := by
          intro hp0
          apply hz
          rw [hp0, diff_zero]
        have hlt : (diff c p).natDegree < n := by
          rw [← hn]
          exact natDegree_lt_natDegree hz (diff_degree_lt c p hp)
        obtain ⟨N, hN, he⟩ := ih (diff c p).natDegree hlt (diff c p) rfl
        refine ⟨N + 1, by omega, ?_⟩
        simpa only [Function.iterate_succ_apply] using he
  exact aux p.natDegree p rfl

lemma E_identity (c : R) (p q : R[X]) :
    diff c (p * q) = diff c p * q + p * diff c q - diff c p * diff c q := by
  simp only [diff, shift, mul_comp]
  ring

lemma even_image (m : ℕ) (hm : 1 ≤ m) : (X ^ 2 : R[X]) ^ m ∈ image 1 := by
  have hh : (LNEDPilot.H (2 * m)).eval (1 / 2 : ℚ) = 0 := by
    simp only [LNEDPilot.H, eval_mul, eval_C, eval_sub]
    rw [(LNEDPilot.bernoulli_half_gap_all m hm).1, mul_zero]
  simpa only [pow_mul] using (monomial_image_iff (R := R) (2 * m)).mpr hh

lemma odd_not_image (m : ℕ) (hm : 1 ≤ m) :
    (X : R[X]) * (X ^ 2 : R[X]) ^ m ∉ image 1 := by
  have hn : ((2 * m + 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hg : (LNEDPilot.H (2 * m + 1)).eval (1 / 2 : ℚ) ≠ 0 := by
    simp only [LNEDPilot.H, eval_mul, eval_C, eval_sub]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    exact mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero hn))
      (LNEDPilot.bernoulli_half_gap_all m hm).2
  intro hv
  have hpow : (X : R[X]) * (X ^ 2 : R[X]) ^ m = X ^ (2 * m + 1) := by
    rw [pow_succ (X : R[X]) (2 * m), pow_mul]
    ring
  rw [hpow] at hv
  exact hg ((monomial_image_iff (2 * m + 1)).mp hv)

lemma not_mathieu : ¬ Mathieu (image (1 : R)) := by
  intro hW
  obtain ⟨N, hN⟩ := hW (X ^ 2) (even_image (R := R)) X 1
  have hin := hN (max N 1) (le_max_left N 1)
  have hout := odd_not_image (R := R) (max N 1) (le_max_right N 1)
  exact hout (by simpa only [mul_one] using hin)

theorem unit_endpoint : UnitEndpoint R :=
  ⟨locally_nilpotent 1, E_identity 1, even_image, odd_not_image, not_mathieu⟩

/-- Specialization to every characteristic-zero field. -/
theorem field_endpoint (K : Type*) [Field K] [CharZero K] : UnitEndpoint K := unit_endpoint

#print axioms unit_endpoint
#print axioms field_endpoint
end LNEDExtension
