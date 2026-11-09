import ABC.S4.Defs

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4.FinalAux

theorem polarPt_apply_zero (r ψ : ℝ) : polarPt r ψ 0 = r * Real.cos ψ := by
  simp [polarPt]

theorem polarPt_apply_one (r ψ : ℝ) : polarPt r ψ 1 = r * Real.sin ψ := by
  simp [polarPt]

theorem dist_polarPt_sq (r r' ψ ψ' : ℝ) :
    dist (polarPt r ψ) (polarPt r' ψ') ^ 2 =
      (r * Real.cos ψ - r' * Real.cos ψ') ^ 2 + (r * Real.sin ψ - r' * Real.sin ψ') ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, polarPt_apply_zero, polarPt_apply_one, Real.dist_eq, sq_abs]

theorem norm_polarPt (r ψ : ℝ) : ‖polarPt r ψ‖ = |r| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, polarPt_apply_zero, polarPt_apply_one, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  have := Real.sin_sq_add_cos_sq ψ
  linear_combination r ^ 2 * this

theorem abs_abs_sub_le_dist_polarPt (r r' ψ ψ' : ℝ) :
    |(|r| - |r'|)| ≤ dist (polarPt r ψ) (polarPt r' ψ') := by
  rw [← norm_polarPt r ψ, ← norm_polarPt r' ψ', dist_eq_norm]
  exact abs_norm_sub_norm_le _ _

theorem abs_sub_le_dist_polarPt (r r' ψ ψ' : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    |r - r'| ≤ dist (polarPt r ψ) (polarPt r' ψ') := by
  have := abs_abs_sub_le_dist_polarPt r r' ψ ψ'
  rwa [abs_of_nonneg hr, abs_of_nonneg hr'] at this

theorem angle_le_dist_polarPt {r r' ψ ψ' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (hψ : |ψ - ψ'| ≤ π) :
    min r r' * (2 / π) * |ψ - ψ'| ≤ dist (polarPt r ψ) (polarPt r' ψ') := by
  set m := min r r' with hm
  set d := ψ - ψ' with hd
  have hm0 : 0 ≤ m := le_min hr hr'
  have hmr : m ≤ r := min_le_left _ _
  have hmr' : m ≤ r' := min_le_right _ _
  have hπ : 0 < π := Real.pi_pos
  set s := Real.sin (|d| / 2) with hs
  set t := 2 / π * (|d| / 2) with ht
  have ht0 : 0 ≤ t := by positivity
  have hts : t ≤ s := Real.mul_le_sin (by positivity) (by linarith)
  have hcosd : Real.cos d = 1 - 2 * s ^ 2 := by
    rw [← Real.cos_abs, hs]
    have h2 : |d| = 2 * (|d| / 2) := by ring
    rw [h2, Real.cos_two_mul, mul_div_cancel_left₀ _ (two_ne_zero)]
    have := Real.sin_sq_add_cos_sq (|d| / 2)
    linarith
  have hcs : Real.cos d = Real.cos ψ * Real.cos ψ' + Real.sin ψ * Real.sin ψ' := Real.cos_sub _ _
  have h1 : t ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ ht0 hts 2
  have h2 : m ^ 2 ≤ r * r' := by nlinarith
  have h3 : m ^ 2 * t ^ 2 ≤ r * r' * s ^ 2 :=
    mul_le_mul h2 h1 (by positivity) (by positivity)
  have hdist := dist_polarPt_sq r r' ψ ψ'
  have hc := Real.sin_sq_add_cos_sq ψ
  have hc' := Real.sin_sq_add_cos_sq ψ'
  have hlhs : (m * (2 / π) * |d|) ^ 2 = 4 * (m ^ 2 * t ^ 2) := by
    rw [ht]; ring
  have hge : (m * (2 / π) * |d|) ^ 2 ≤ dist (polarPt r ψ) (polarPt r' ψ') ^ 2 := by
    have hexp : (r * Real.cos ψ - r' * Real.cos ψ') ^ 2 + (r * Real.sin ψ - r' * Real.sin ψ') ^ 2
        = (r - r') ^ 2 + 4 * (r * r' * s ^ 2) := by
      linear_combination r ^ 2 * hc + r' ^ 2 * hc' + 2 * r * r' * hcs - 2 * r * r' * hcosd
    rw [hlhs, hdist, hexp]
    nlinarith [sq_nonneg (r - r')]
  exact (pow_le_pow_iff_left₀ (by positivity) dist_nonneg two_ne_zero).1 hge

theorem polarPt_add_int (r ψ : ℝ) (k : ℤ) : polarPt r (ψ + 2 * π * k) = polarPt r ψ := by
  have : ψ + 2 * π * k = ψ + k * (2 * π) := by ring
  simp only [polarPt, this, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem polarW_ofReal {P θ : ℝ} (hP : 0 ≤ P) :
    polarW (P : ℂ) (θ : ℂ) = ofR (polarPt (Real.sqrt (2 * P)) (-θ)) := by
  have h2P : (0 : ℝ) ≤ 2 * P := by positivity
  have hsq : ((Real.sqrt (2 * P) : ℝ) : ℂ) = (2 * (P : ℂ)) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h2P]
    push_cast; rfl
  funext i
  fin_cases i
  · show (2 * (P : ℂ)) ^ (1 / 2 : ℂ) * Complex.cos θ = ((polarPt (√(2 * P)) (-θ) 0 : ℝ) : ℂ)
    rw [polarPt_apply_zero, Complex.ofReal_mul, hsq, Real.cos_neg, Complex.ofReal_cos]
  · show -((2 * (P : ℂ)) ^ (1 / 2 : ℂ) * Complex.sin θ) = ((polarPt (√(2 * P)) (-θ) 1 : ℝ) : ℂ)
    rw [polarPt_apply_one, Complex.ofReal_mul, hsq, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_sin]
    simp

theorem ofR_injective : Function.Injective ofR := by
  intro x y h
  ext i
  exact Complex.ofReal_injective (congrFun h i)

theorem exists_int_abs_sub_le (x y : ℝ) : ∃ k : ℤ, |x - (y + 2 * π * k)| ≤ π := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨round ((x - y) / (2 * π)), ?_⟩
  have h := abs_sub_round ((x - y) / (2 * π))
  have heq : x - (y + 2 * π * (round ((x - y) / (2 * π)) : ℝ)) =
      (2 * π) * ((x - y) / (2 * π) - round ((x - y) / (2 * π))) := by
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos (by positivity)]
  nlinarith

end ABC.S4.FinalAux
