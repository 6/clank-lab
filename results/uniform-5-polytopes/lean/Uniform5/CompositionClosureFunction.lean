import Uniform5.Closure

/-!
# The paper's reciprocal-radius closure function

This is the literal real function used in S1 and ROOT. Its relation to the
previous geometric cosine-law/once-around theorem is proved here. Applying
it to a polytope still requires the actual transverse-ray constructor.
-/
noncomputable section
namespace Uniform5.Composition
open InnerProductGeometry
open scoped BigOperators

/-- Cosine of the polar angle, with reciprocal circumradius s. -/
noncomputable def cyclePolarCosine (ρ d s : ℝ) : ℝ :=
  d * s / Real.sqrt (1 - ρ ^ 2 * s ^ 2)

/-- The literal closure function g(s) from the paper. Its domain restrictions
are applied separately by S1 and the geometric realization theorem. -/
noncomputable def cycleClosureFunction (n : ℕ) (ρ : ℝ) (d α : ℕ → ℝ) (s : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.arccos
    ((Real.cos (α i) - cyclePolarCosine ρ (d i) s * cyclePolarCosine ρ (d (i + 1)) s) /
      (Real.sqrt (1 - cyclePolarCosine ρ (d i) s ^ 2) *
        Real.sqrt (1 - cyclePolarCosine ρ (d (i + 1)) s ^ 2)))) - 2 * Real.pi

/-- The infinite-radius endpoint retains the flat-cycle root, which is
why the separate geometric flat-cycle exclusion is necessary. -/
theorem cycleClosureFunction_at_zero (n : ℕ) (ρ : ℝ) (d α : ℕ → ℝ)
    (hα : ∀ i < n, 0 ≤ α i ∧ α i ≤ Real.pi) :
    cycleClosureFunction n ρ d α 0 = (∑ i ∈ Finset.range n, α i) - 2 * Real.pi := by
  unfold cycleClosureFunction
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [cyclePolarCosine, mul_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, Real.sqrt_one, zero_div, mul_one, div_one]
  exact Real.arccos_cos (hα i (Finset.mem_range.mp hi)).1
    (hα i (Finset.mem_range.mp hi)).2

/-- A concrete flat three-cycle has the spurious infinite-radius root. -/
theorem flat_three_cycle_zero (ρ : ℝ) (d : ℕ → ℝ) :
    cycleClosureFunction 3 ρ d (fun _ => 2 * Real.pi / 3) 0 = 0 := by
  rw [cycleClosureFunction_at_zero _ _ _ _ (fun _ _ => by
    constructor <;> nlinarith [Real.pi_pos])]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Substituting s=1/R gives the actual projected height denominator. -/
theorem cyclePolarCosine_at_radius {ρ d R h : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hsq : h ^ 2 = R ^ 2 - ρ ^ 2) :
    cyclePolarCosine ρ d (1 / R) = d / h := by
  have hden : Real.sqrt (1 - ρ ^ 2 * (1 / R) ^ 2) = h / R := by
    have heq : 1 - ρ ^ 2 * (1 / R) ^ 2 = (h / R) ^ 2 := by
      field_simp
      nlinarith
    rw [heq, Real.sqrt_sq (by positivity)]
  rw [cyclePolarCosine, hden]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The geometric closure theorem implies a zero of the actual numerical
closure function, with no independently assumed closure root. -/
theorem cycleClosureFunction_zero_of_fan {n : ℕ} {w : E} {u : ℕ → E}
    {ρ R h : ℝ} {d α : ℕ → ℝ}
    (hn : 0 < n) (hw : ‖w‖ = 1) (hu : ∀ i < n, ‖u i‖ = 1)
    (hcyclic : u n = u 0) (htangent : ∀ i < n, sphericalTangent w (u i) ≠ 0)
    (fan : SphericalFanData n
      (fun i => angle (sphericalTangent w (u i)) (sphericalTangent w (u (i + 1)))))
    (hR : 0 < R) (hh : 0 < h) (hsq : h ^ 2 = R ^ 2 - ρ ^ 2)
    (hpolar : ∀ i ≤ n, Real.cos (angle (u i) w) = d i / h)
    (hangle : ∀ i < n, α i = angle (u i) (u (i + 1))) :
    cycleClosureFunction n ρ d α (1 / R) = 0 := by
  have hcos (i : ℕ) (hi : i ≤ n) :
      cyclePolarCosine ρ (d i) (1 / R) = Real.cos (angle (u i) w) := by
    rw [cyclePolarCosine_at_radius hR hh hsq, hpolar i hi]
  have hsin (i : ℕ) (hi : i ≤ n) :
      Real.sqrt (1 - cyclePolarCosine ρ (d i) (1 / R) ^ 2) =
        Real.sin (angle (u i) w) := by
    rw [hcos i hi]
    exact (Real.sin_eq_sqrt_one_sub_cos_sq (angle_nonneg _ _) (angle_le_pi _ _)).symm
  have hclosure := (closure_equation hn hw hu hcyclic htangent fan).2
  unfold cycleClosureFunction
  apply sub_eq_zero.mpr
  convert hclosure using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [hsin i (by omega), hsin (i + 1) (by omega),
    hangle i hin, hcos i (by omega), hcos (i + 1) (by omega)]

end Uniform5.Composition
