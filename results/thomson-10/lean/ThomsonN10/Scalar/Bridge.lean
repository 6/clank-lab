/- Adapted from proof/lean/ThomsonN9/Bernstein/Minorant.lean and MinorantCert.lean,
   aravindkarthigeyan/thomson-n9-lean, MIT, commit
   168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Scalar.CertificateData
import ThomsonN10.Interfaces
set_option maxRecDepth 100000
namespace ThomsonN10.Scalar
open Bernstein
theorem sqrt_subst {t : ℝ} (ht : t < 1) :
    0 < Real.sqrt ((1 - t) / 2) ∧ 1 - 2 * Real.sqrt ((1 - t) / 2) ^ 2 = t ∧
      Real.sqrt (2 - 2 * t) = 2 * Real.sqrt ((1 - t) / 2) := by
  have hpos : (0 : ℝ) < (1 - t) / 2 := by linarith
  have hsq := Real.sq_sqrt hpos.le
  refine ⟨Real.sqrt_pos.2 hpos, by rw [hsq]; ring, ?_⟩
  rw [show (2 : ℝ) - 2 * t = 2 ^ 2 * ((1 - t) / 2) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]


theorem minorant_eq (t : ℝ) : minorant t = polyEval numerator t / denominator := by
  norm_num [minorant, hCoeff, minorantEps, numerator, denominator, polyEval,
    Fin.sum_univ_succ]
  <;> ring

theorem potential_bound {t : ℝ} (ht : t < 1) {q : List ℤ} {D : ℤ}
    (hD : (0 : ℝ) < D)
    (hp : 0 ≤ polyEval (potential q D) (Real.sqrt ((1-t)/2))) :
    polyEval q t / D ≤ (Real.sqrt (2-2*t))⁻¹ := by
  obtain ⟨hy, hyt, hs⟩ := sqrt_subst ht
  rw [polyEval_potential, hyt] at hp
  rw [hs, div_le_iff₀ hD, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
  linarith

def extOk (A B M : ℤ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ A) && decide (0 ≤ B) && decide (hi < 1) &&
    decide ((A : ℚ) * A ≤ (M : ℚ) * M * ((1 - hi) / 2)) &&
    decide ((M : ℚ) * M * ((1 - lo) / 2) ≤ (B : ℚ) * B)
theorem extOk_sound {A B M : ℤ} {lo hi : ℚ} (h : extOk A B M lo hi = true) (hM : 0 < M)
    {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    t < 1 ∧ (A : ℝ) ≤ M * Real.sqrt ((1 - t) / 2) ∧ (M : ℝ) * Real.sqrt ((1 - t) / 2) ≤ B := by
  simp only [extOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hhi⟩, hlo2⟩, hhi2⟩ := h
  have hA' : (0 : ℝ) ≤ A := by exact_mod_cast hA
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hhi' : (hi : ℝ) < 1 := by exact_mod_cast hhi
  have hlo2' : (A : ℝ) * A ≤ (M : ℝ) * M * ((1 - (hi : ℝ)) / 2) := by exact_mod_cast hlo2
  have hhi2' : (M : ℝ) * M * ((1 - (lo : ℝ)) / 2) ≤ (B : ℝ) * B := by exact_mod_cast hhi2
  have ht1 : t < 1 := lt_of_le_of_lt h2 hhi'
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hpos : (0 : ℝ) ≤ (1 - t) / 2 := by linarith
  have hy0 : 0 ≤ Real.sqrt ((1 - t) / 2) := Real.sqrt_nonneg _
  have hyy : Real.sqrt ((1 - t) / 2) * Real.sqrt ((1 - t) / 2) = (1 - t) / 2 :=
    Real.mul_self_sqrt hpos
  have hMy : (M * Real.sqrt ((1 - t) / 2)) * (M * Real.sqrt ((1 - t) / 2))
      = (M : ℝ) * M * ((1 - t) / 2) :=
    calc (M * Real.sqrt ((1 - t) / 2)) * (M * Real.sqrt ((1 - t) / 2))
        = (M : ℝ) * M * (Real.sqrt ((1 - t) / 2) * Real.sqrt ((1 - t) / 2)) := by ring
      _ = (M : ℝ) * M * ((1 - t) / 2) := by rw [hyy]
  have hMy0 : 0 ≤ (M : ℝ) * Real.sqrt ((1 - t) / 2) := mul_nonneg hM'.le hy0
  have hMM : (0 : ℝ) ≤ (M : ℝ) * M := mul_nonneg hM'.le hM'.le
  refine ⟨ht1, ?_, ?_⟩
  · rw [mul_self_le_mul_self_iff hA' hMy0, hMy]
    calc (A : ℝ) * A ≤ (M : ℝ) * M * ((1 - (hi : ℝ)) / 2) := hlo2'
      _ ≤ (M : ℝ) * M * ((1 - t) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hMM
  · rw [mul_self_le_mul_self_iff hMy0 hB', hMy]
    calc (M : ℝ) * M * ((1 - t) / 2) ≤ (M : ℝ) * M * ((1 - (lo : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hMM
      _ ≤ (B : ℝ) * B := hhi2'


theorem gap_of_checks {t : ℝ} {A B M d : ℤ} {fuel bits : ℕ} {lo hi : ℚ}
    (hc : checkInterval gapPoly A B M d fuel bits = true)
    (hs : extOk A B M lo hi = true) (hM : 0 < M)
    (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ (hi : ℝ)) :
    (gapBound : ℝ) ≤ (Real.sqrt (2-2*t))⁻¹ - minorant t := by
  obtain ⟨ht, ha, hb⟩ := extOk_sound hs hM h1 h2
  have hp := checkInterval_sound hc _ ha hb
  have hD : (0 : ℝ) < denominator := by norm_num [denominator]
  have h := potential_bound ht hD hp
  rw [polyEval_addL] at h
  simp only [polyEval_cons, polyEval_nil, mul_zero, add_zero] at h
  rw [add_div, ← minorant_eq] at h
  have hg : (gapBound : ℝ) ≤ (gapNumerator : ℝ) / denominator := by
    norm_num [gapBound, gapNumerator, denominator]
  linarith
end ThomsonN10.Scalar
