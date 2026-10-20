import Uniform5.CompositionCaseBCycleTypes
import Uniform5.CompositionPolyhedronRadius

/-! The literal geometric closure specializes to the type-(i) circle equation. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped BigOperators

/-- The equal-height polar denominator is the actual transverse circle radius. -/
theorem halfHeight_circle {ρ R : ℝ} (hR : 0 < R)
    (hd : 0 < 1 - ρ ^ 2 * (1 / R) ^ 2)
    (hS : 0 < Real.sqrt (1 - cyclePolarCosine ρ (1 / 2) (1 / R) ^ 2)) :
    let S := Real.sqrt (1 - cyclePolarCosine ρ (1 / 2) (1 / R) ^ 2)
    0 < S ∧ S < 1 ∧ CaseB.radiusFromCircle S ^ 2 = R ^ 2 - ρ ^ 2 := by
  dsimp only
  let p := cyclePolarCosine ρ (1 / 2) (1 / R)
  let S := Real.sqrt (1 - p ^ 2)
  have hp : 0 < p := by
    dsimp [p, cyclePolarCosine]
    positivity
  have hSq : S ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (Real.sqrt_pos.mp hS).le
  have hS1 : S < 1 := by
    have hSn : 0 ≤ S := Real.sqrt_nonneg _
    nlinarith [sq_pos_of_pos hp]
  have hden : 1 - ρ ^ 2 * (1 / R) ^ 2 = (R ^ 2 - ρ ^ 2) / R ^ 2 := by
    field_simp
  have hH : 0 < R ^ 2 - ρ ^ 2 := by
    rw [hden] at hd
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hR)).mp hd
  have hpq : p ^ 2 = 1 / (4 * (R ^ 2 - ρ ^ 2)) := by
    dsimp [p, cyclePolarCosine]
    rw [div_pow, mul_pow, Real.sq_sqrt hd.le, hden]
    field_simp
    <;> ring
  refine ⟨hS, hS1, ?_⟩
  change CaseB.radiusFromCircle S ^ 2 = _
  rw [CaseB.radiusFromCircle_sq (Real.sqrt_nonneg _) hS1, hSq, hpq]
  field_simp

/-- A facet radius strictly below the parent radius makes every circle
chord a strict minor chord. -/
theorem polygonCos_lt_circle_of_radius {q : ℕ} {S : ℝ}
    (hq : 3 ≤ q) (hS : 0 ≤ S) (hS1 : S < 1)
    (hr : unitPolygonRadius q ^ 2 < CaseB.radiusFromCircle S ^ 2) :
    CaseB.polygonCos q < S := by
  by_contra h
  have hh := CaseB.radiusFromCircle_mono hS (le_of_not_gt h)
    (CaseB.polygonCos_bounds hq).2
  rw [CaseB.radiusFromCircle_polygonCos hq] at hh
  change CaseB.radiusFromCircle S ≤ unitPolygonRadius q at hh
  have hp := CaseB.radiusFromCircle_pos hS hS1
  have hqpos := unitPolygonRadius_pos hq
  nlinarith

/-- Principal inverse cosine of the double-angle expression. -/
theorem arccos_one_sub_two_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arccos (1 - 2 * x ^ 2) = 2 * Real.arcsin x := by
  have hsq : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hc : Real.cos (2 * Real.arcsin x) = 1 - 2 * x ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_arcsin, Real.sq_sqrt hsq]
    ring
  rw [← hc, Real.arccos_cos]
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hx)
  · linarith [Real.arcsin_le_pi_div_two x]

/-- The equal-height spherical-cosine summand is exactly the paper's
arcsine summand, including its principal branch. -/
theorem halfHeight_summand {q : ℕ} {p S : ℝ} (hq : 3 ≤ q)
    (hS : 0 < S) (hSq : S ^ 2 = 1 - p ^ 2) (hch : CaseB.polygonCos q < S) :
    Real.arccos ((Real.cos (Real.pi * (1 - 2 / (q : ℝ))) - p * p) /
      (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - p ^ 2))) =
      CaseB.centralArc (CaseB.polygonCos q) S := by
  have hsqrt : Real.sqrt (1 - p ^ 2) = S := by rw [← hSq, Real.sqrt_sq hS.le]
  have he : Real.pi * (1 - 2 / (q : ℝ)) = Real.pi - 2 * (Real.pi / (q : ℝ)) := by ring
  have hcos : Real.cos (Real.pi * (1 - 2 / (q : ℝ))) = 1 - 2 * CaseB.polygonCos q ^ 2 := by
    rw [he, Real.cos_pi_sub, Real.cos_two_mul]
    unfold CaseB.polygonCos
    ring
  have harg : (Real.cos (Real.pi * (1 - 2 / (q : ℝ))) - p * p) /
      (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - p ^ 2)) =
      1 - 2 * (CaseB.polygonCos q / S) ^ 2 := by
    rw [hsqrt, hcos]
    field_simp
    nlinarith [hSq]
  rw [harg]
  exact arccos_one_sub_two_sq (div_nonneg (CaseB.polygonCos_bounds hq).1.le hS.le)
    ((div_le_one hS).mpr hch.le)

end Uniform5.Composition
