import D1
import D3

namespace LNEDPilot
open Polynomial

lemma even_power_image (m : ℕ) (hm : 1 ≤ m) : (X ^ 2 : ℚ[X]) ^ m ∈ V := by
  have hh : (H (2 * m)).eval (1 / 2 : ℚ) = 0 := by
    simp only [H, eval_mul, eval_C, eval_sub]
    rw [(bernoulli_half_gap_all m hm).1, mul_zero]
  have hx := (monomial_image_iff (2 * m)).mpr hh
  simpa only [pow_mul] using hx

lemma odd_power_not_image (m : ℕ) (hm : 1 ≤ m) :
    (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ m ∉ V := by
  have hn : ((2 * m + 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hg : (H (2 * m + 1)).eval (1 / 2 : ℚ) ≠ 0 := by
    simp only [H, eval_mul, eval_C, eval_sub]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    exact mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero hn))
      (bernoulli_half_gap_all m hm).2
  intro hv
  have hpow : (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ m = X ^ (2 * m + 1) := by
    rw [pow_succ (X : ℚ[X]) (2 * m), pow_mul]
    ring
  rw [hpow] at hv
  exact hg ((monomial_image_iff (2 * m + 1)).mp hv)

/-- The full original finite-polynomial endpoint, with no unresolved premises. -/
theorem endpoint_proved : ENDPOINT := by
  refine ⟨?_, delta_E, even_power_image, odd_power_not_image⟩
  intro h
  obtain ⟨N, _, he⟩ := delta_locally_nilpotent h
  exact ⟨N, he⟩

#print axioms endpoint_proved
end LNEDPilot
