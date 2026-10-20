import Uniform5.Centroid
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# The geometric closure equation

The metric and interior arguments are proved here. Two missing spherical
polygon inputs are recorded as data: `PolarPolygonData` (polar duality and
positive spherical excess), and `SphericalFanData` (an ordered, once-around
lift of the tangent directions). No constructor from a cone is asserted.
-/
noncomputable section
namespace Uniform5
open Set InnerProductGeometry
open scoped RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Component of a spherical vertex in the tangent plane at a unit pole. -/
def sphericalTangent (w u : E) : E := u - ⟪u, w⟫ • w

/-- Inner product of tangent components, derived in the ambient space. -/
theorem sphericalTangent_inner {w u v : E} (hw : ‖w‖ = 1) :
    ⟪sphericalTangent w u, sphericalTangent w v⟫ =
      ⟪u, v⟫ - ⟪u, w⟫ * ⟪v, w⟫ := by
  simp only [sphericalTangent, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hw]
  rw [real_inner_comm w v]
  ring

/-- The tangent component has length the sine of the polar angle. -/
theorem sphericalTangent_norm {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    ‖sphericalTangent w u‖ = Real.sin (angle u w) := by
  have hi := sphericalTangent_inner (u := u) (v := u) hw
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu] at hi
  have hc : Real.cos (angle u w) = ⟪u, w⟫ := by simp [cos_angle, hu, hw]
  have ht := Real.sin_sq_add_cos_sq (angle u w)
  rw [hc] at ht
  have hn := norm_nonneg (sphericalTangent w u)
  have hs := sin_angle_nonneg u w
  nlinarith

/-- The spherical cosine law from projected tangent vectors; the angle at the
pole is the actual Euclidean angle between those vectors. -/
theorem spherical_cosine_law {w u v : E}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (angle (sphericalTangent w u) (sphericalTangent w v)) =
      (Real.cos (angle u v) - Real.cos (angle u w) * Real.cos (angle v w)) /
        (Real.sin (angle u w) * Real.sin (angle v w)) := by
  rw [cos_angle, sphericalTangent_inner hw, sphericalTangent_norm hw hu,
    sphericalTangent_norm hw hv]
  simp only [cos_angle, hu, hv, hw, mul_one, div_one]

/-- Orthogonal projection onto a cell ray gives the centre's dot product. -/
theorem cell_ray_inner {w u : E} {d : ℝ} (hu : ‖u‖ = 1)
    (hprojection : ⟪w - d • u, u⟫ = 0) : ⟪w, u⟫ = d := by
  simpa [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu,
    sub_eq_zero] using hprojection

/-- Part (b): polar cosine is projected distance divided by height. -/
theorem cell_polar_cosine {w u : E} {d h : ℝ} (hu : ‖u‖ = 1)
    (hw : ‖w‖ = h) (hprojection : ⟪w - d • u, u⟫ = 0) :
    Real.cos (angle u w) = d / h := by
  have hd : ⟪u, w⟫ = d := by
    rw [real_inner_comm]
    exact cell_ray_inner hu hprojection
  rw [cos_angle, hd, hu, hw, one_mul]

/-- A normalized nonzero centre is a unit spherical pole. -/
theorem normalized_center_unit {w : E} {h : ℝ} (hw : ‖w‖ = h) (hh : 0 < h) :
    ‖h⁻¹ • w‖ = 1 := by
  simp [norm_smul, hw, abs_of_pos hh, ne_of_gt hh]

/-- The projected positive cell offset forces a nonzero centre height. -/
theorem cell_height_pos {w u : E} {d : ℝ} (hu : ‖u‖ = 1)
    (hd : 0 < d) (hprojection : ⟪w - d • u, u⟫ = 0) : 0 < ‖w‖ := by
  apply norm_pos_iff.mpr
  intro hw
  have h := cell_ray_inner hu hprojection
  rw [hw, inner_zero_left] at h
  linarith

/-- Normalizing the centre preserves the polar cosine used in closure. -/
theorem normalized_cell_polar_cosine {w u : E} {d h : ℝ}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = h) (hh : 0 < h)
    (hprojection : ⟪w - d • u, u⟫ = 0) :
    Real.cos (angle u (h⁻¹ • w)) = d / h := by
  rw [angle_smul_right_of_pos u w (inv_pos.mpr hh)]
  exact cell_polar_cosine hu hw hprojection

/-- Nonzero tangent rays make the denominator of the cosine law positive. -/
theorem spherical_denominator_pos {w u v : E}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huT : sphericalTangent w u ≠ 0) (hvT : sphericalTangent w v ≠ 0) :
    0 < Real.sin (angle u w) * Real.sin (angle v w) := by
  rw [← sphericalTangent_norm hw hu, ← sphericalTangent_norm hw hv]
  exact mul_pos (norm_pos_iff.mpr huT) (norm_pos_iff.mpr hvT)

/-- Missing spherical geometry input: polar angles are supplements of original
side lengths and have positive spherical excess. Constructing this data from
a pointed full-dimensional polyhedral 3-cone remains an explicit obligation. -/
structure PolarPolygonData {ι : Type*} [Fintype ι] (α : ι → ℝ) where
  polarAngle : ι → ℝ
  dual_angles : ∀ i, α i + polarAngle i = Real.pi
  positive_excess : ((Fintype.card ι : ℝ) - 2) * Real.pi < ∑ i, polarAngle i

/-- Part (a): polar duality and positive excess give strict perimeter. -/
theorem strict_spherical_perimeter {ι : Type*} [Fintype ι] {α : ι → ℝ}
    (polar : PolarPolygonData α) : ∑ i, α i < 2 * Real.pi := by
  have hsum : (∑ i, α i) + ∑ i, polar.polarAngle i =
      (Fintype.card ι : ℝ) * Real.pi := by
    rw [← Finset.sum_add_distrib]
    simp [polar.dual_angles]
  have hpos := polar.positive_excess
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- The centre maps into the interior of the transverse cone under an open
quotient map. Cone containment is a set inclusion, not an interior premise. -/
theorem center_mem_interior_transverse_cone
    {F : Type*} [TopologicalSpace F] {P : Set E} {T : Set F}
    {c : E} {π : E → F} (hopen : IsOpenMap π)
    (hcone : π '' P ⊆ T) (hc : c ∈ interior P) : π c ∈ interior T :=
  interior_mono hcone (hopen.image_interior_subset P ⟨c, hc, rfl⟩)

/-- Connect the previously proved centroid theorem to transverse interiority.
An affine quotient can be used here, so the original centroid may be zero
while the projected displacement from the face centre is nonzero. -/
theorem centroid_mem_interior_transverse_cone
    {ι F : Type*} [Fintype ι] [TopologicalSpace F]
    (p : ι → E) (hsum : ∑ i, p i = 0)
    (hne : (interior (convexHull ℝ (range p))).Nonempty)
    {π : E → F} {T : Set F} (hopen : IsOpenMap π)
    (hcone : π '' convexHull ℝ (range p) ⊆ T) : π 0 ∈ interior T :=
  center_mem_interior_transverse_cone hopen hcone
    (zero_mem_interior_convexHull_of_sum_zero p hsum hne)

/-- A surjective continuous linear quotient is open, removing the open-map
premise for Euclidean transverse cones. Translate the face centre to zero. -/
theorem center_mem_interior_linear_cone [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (π : E →L[ℝ] F) (hsurj : Function.Surjective π)
    {P : Set E} {T : Set F} {c : E}
    (hcone : π '' P ⊆ T) (hc : c ∈ interior P) : π c ∈ interior T :=
  center_mem_interior_transverse_cone (π.isOpenMap hsurj) hcone hc

/-- Missing fan-order input: an angular lift with gaps strictly between zero
and pi whose terminal value is one full turn later. In the application its
gaps are the actual angles between consecutive tangent directions. -/
structure SphericalFanData (n : ℕ) (θ : ℕ → ℝ) where
  lift : ℕ → ℝ
  gap : ∀ i < n, θ i = lift (i + 1) - lift i
  gap_pos : ∀ i < n, 0 < lift (i + 1) - lift i
  gap_lt_pi : ∀ i < n, lift (i + 1) - lift i < Real.pi
  winding : lift n = lift 0 + 2 * Real.pi

/-- The once-around fan telescopes, giving strict triangle angles and closure. -/
theorem spherical_fan_closure {n : ℕ} {θ : ℕ → ℝ} (fan : SphericalFanData n θ) :
    (∀ i < n, 0 < θ i ∧ θ i < Real.pi) ∧
      ∑ i ∈ Finset.range n, θ i = 2 * Real.pi := by
  constructor
  · intro i hi
    rw [fan.gap i hi]
    exact ⟨fan.gap_pos i hi, fan.gap_lt_pi i hi⟩
  · calc
      ∑ i ∈ Finset.range n, θ i =
          ∑ i ∈ Finset.range n, (fan.lift (i + 1) - fan.lift i) :=
        Finset.sum_congr rfl (fun i hi => fan.gap i (Finset.mem_range.mp hi))
      _ = fan.lift n - fan.lift 0 := Finset.sum_range_sub fan.lift n
      _ = 2 * Real.pi := by rw [fan.winding]; ring

/-- A ray through the pole has zero tangent component, so it is not an
admissible ray in the nondegenerate cycle theorem below. -/
theorem sphericalTangent_self {w : E} (hw : ‖w‖ = 1) :
    sphericalTangent w w = 0 := by
  simp [sphericalTangent, real_inner_self_eq_norm_sq, hw]

/-- Part (c), in the arccos form used by the closure checker. This is a closed
cycle of unit rays with nonzero tangent components; unlike a bare angle sum,
these conditions exclude Lean's totalized angle at the zero vector. The
missing geometric step constructs the fan lift from a convex link and pole. -/
theorem closure_equation {n : ℕ} {w : E} {u : ℕ → E}
    (hn : 0 < n) (hw : ‖w‖ = 1) (hu : ∀ i < n, ‖u i‖ = 1)
    (hcyclic : u n = u 0) (htangent : ∀ i < n, sphericalTangent w (u i) ≠ 0)
    (fan : SphericalFanData n
      (fun i => angle (sphericalTangent w (u i)) (sphericalTangent w (u (i + 1))))) :
    (∀ i < n, 0 < Real.sin (angle (u i) w) * Real.sin (angle (u (i + 1)) w)) ∧
    (∑ i ∈ Finset.range n,
      Real.arccos ((Real.cos (angle (u i) (u (i + 1))) -
        Real.cos (angle (u i) w) * Real.cos (angle (u (i + 1)) w)) /
        (Real.sin (angle (u i) w) * Real.sin (angle (u (i + 1)) w))) =
      2 * Real.pi) := by
  have hu' : ∀ i ≤ n, ‖u i‖ = 1 := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | rfl
    · exact hu i h
    · rw [hcyclic]; exact hu 0 hn
  have ht' : ∀ i ≤ n, sphericalTangent w (u i) ≠ 0 := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | rfl
    · exact htangent i h
    · rw [hcyclic]; exact htangent 0 hn
  constructor
  · intro i hi
    exact spherical_denominator_pos hw (hu' i (by omega)) (hu' (i + 1) (by omega))
      (ht' i (by omega)) (ht' (i + 1) (by omega))
  · rw [← (spherical_fan_closure fan).2]
    apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [← spherical_cosine_law hw (hu' i (by omega)) (hu' (i + 1) (by omega))]
    exact Real.arccos_cos (angle_nonneg _ _) (angle_le_pi _ _)

end Uniform5
