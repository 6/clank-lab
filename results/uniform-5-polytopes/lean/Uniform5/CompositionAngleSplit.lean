import Uniform5.CompositionPolarMetrics
import Mathlib.Geometry.Euclidean.Triangle

/-! The angular splitting used by the paper's word-angle lemma. -/
noncomputable section
namespace Uniform5.Composition
open InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero positive combination lies angularly between its two rays.
This is the ordinary triangle angle sum, with no oriented-angle premise. -/
theorem angle_split_of_positive_combination {u v w : E} {s t : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hs : 0 < s) (ht : 0 < t)
    (heq : w = s • u + t • v) :
    angle u w + angle w v = angle u v := by
  have hx : s • u ≠ 0 := smul_ne_zero hs.ne' hu
  have h := angle_add_angle_sub_add_angle_sub_eq_pi hx hw
  have hsub : s • u - w = -(t • v) := by rw [heq]; abel
  have hsub' : w - s • u = t • v := by rw [heq]; abel
  rw [hsub, hsub', angle_neg_right,
    angle_smul_left_of_pos _ _ hs, angle_smul_left_of_pos _ _ hs,
    angle_smul_right_of_pos _ _ ht, angle_smul_right_of_pos _ _ ht] at h
  linarith

/-- Once the actual center is between the cell rays, their polar cosines
alone determine the whole wedge angle. -/
theorem angle_split_arccos {u v w : E} {s t cu cv : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hs : 0 < s) (ht : 0 < t)
    (heq : w = s • u + t • v)
    (hcu : Real.cos (angle u w) = cu) (hcv : Real.cos (angle v w) = cv) :
    angle u v = Real.arccos cu + Real.arccos cv := by
  rw [← hcu, ← hcv, Real.arccos_cos (angle_nonneg _ _) (angle_le_pi _ _),
    Real.arccos_cos (angle_nonneg _ _) (angle_le_pi _ _), angle_comm v w]
  exact (angle_split_of_positive_combination hu hw hs ht heq).symm

/-- Literal square-root ratio form of `lem:wordangle`. Positive-combination
geometry is kept explicit here until instantiated on the actual 4D link. -/
theorem wedge_angle_from_radii {u v w : E} {s t R rA rB ρ : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hs : 0 < s) (ht : 0 < t)
    (heq : w = s • u + t • v)
    (hrA : 0 ≤ rA ^ 2 - ρ ^ 2) (hrB : 0 ≤ rB ^ 2 - ρ ^ 2)
    (hA : Real.cos (angle u w) = Real.sqrt (rA ^ 2 - ρ ^ 2) / Real.sqrt (R ^ 2 - ρ ^ 2))
    (hB : Real.cos (angle v w) = Real.sqrt (rB ^ 2 - ρ ^ 2) / Real.sqrt (R ^ 2 - ρ ^ 2)) :
    angle u v = Real.arccos (Real.sqrt ((rA ^ 2 - ρ ^ 2) / (R ^ 2 - ρ ^ 2))) +
      Real.arccos (Real.sqrt ((rB ^ 2 - ρ ^ 2) / (R ^ 2 - ρ ^ 2))) := by
  rw [Real.sqrt_div hrA, Real.sqrt_div hrB]
  exact angle_split_arccos hu hw hs ht heq hA hB

end Uniform5.Composition
