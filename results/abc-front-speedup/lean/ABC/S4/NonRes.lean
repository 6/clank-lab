import ABC.S4.Defs

/-! T3: no resonance up to order 4 from the certified trace. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem nonres_of_trace {ν tr : ℝ} (h1 : -19650 / 10000 ≤ tr) (h2 : tr ≤ -19640 / 10000)
    (hν : Real.cos (2 * π * ν) = tr / 2) : NonRes4 ν := by
  intro q hq1 hq4 m hm
  -- `cos (q θ) = 1` at a resonance, with `θ = 2πν`
  have key : Real.cos ((q : ℝ) * (2 * π * ν)) = 1 := by
    rw [show (q : ℝ) * (2 * π * ν) = (m : ℝ) * (2 * π) by rw [← hm]; ring]
    exact Real.cos_int_mul_two_pi m
  -- Chebyshev: `T_q (cos θ) < 1` for `cos θ ∈ [-0.9825, -0.982]`
  have hc1 : -9825 / 10000 ≤ Real.cos (2 * π * ν) := by rw [hν]; linarith
  have hc2 : Real.cos (2 * π * ν) ≤ -9820 / 10000 := by rw [hν]; linarith
  set c := Real.cos (2 * π * ν) with hcdef
  interval_cases q
  · rw [Nat.cast_one, one_mul] at key
    linarith
  · rw [show ((2 : ℕ) : ℝ) * (2 * π * ν) = 2 * (2 * π * ν) by push_cast; ring,
      Real.cos_two_mul, ← hcdef] at key
    nlinarith
  · rw [show ((3 : ℕ) : ℝ) * (2 * π * ν) = 3 * (2 * π * ν) by push_cast; ring,
      Real.cos_three_mul, ← hcdef] at key
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc2)) (sub_nonneg.2 hc2)]
  · rw [show ((4 : ℕ) : ℝ) * (2 * π * ν) = 2 * (2 * (2 * π * ν)) by push_cast; ring,
      Real.cos_two_mul, Real.cos_two_mul, ← hcdef] at key
    have hT2a : 9 / 10 ≤ 2 * c ^ 2 - 1 := by nlinarith
    have hT2b : 2 * c ^ 2 - 1 ≤ 95 / 100 := by nlinarith
    nlinarith

end ABC.S4
