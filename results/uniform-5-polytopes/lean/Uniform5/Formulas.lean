import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! The metric formulas of `lem:vf`, independent of the combinatorial face claims.
The ambient space can in particular be any finite-dimensional Euclidean space.
-/
noncomputable section

namespace Uniform5

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine hyperplane through the unit-distance neighbours of `v`. -/
def figureHyperplane (v : E) (R : ℝ) : Set E :=
  {x | ⟪x, v⟫ = R ^ 2 - 1 / 2}

/-- The centre on the radial axis, valid also when its coefficient is negative. -/
def figureCenter (v : E) (R : ℝ) : E := (1 - 1 / (2 * R ^ 2)) • v

/-- Squared chord length for two points on the same centred sphere. -/
theorem sphere_chord_sq {x v : E} {R : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) :
    ‖x - v‖ ^ 2 = 2 * R ^ 2 - 2 * ⟪x, v⟫ := by
  rw [norm_sub_sq_real, hx, hv]
  ring

/-- Unit chords are exactly the points in the vertex-figure hyperplane. -/
theorem unit_distance_iff_hyperplane {x v : E} {R : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) :
    dist x v = 1 ↔ x ∈ figureHyperplane v R := by
  change dist x v = 1 ↔ ⟪x, v⟫ = R ^ 2 - 1 / 2
  rw [dist_eq_norm]
  have h := sphere_chord_sq hx hv
  have hn := norm_nonneg (x - v)
  constructor <;> intro h'
  · rw [h'] at h
    linarith
  · rw [h'] at h
    nlinarith

/-- Chords longer than one lie strictly below that hyperplane. -/
theorem distance_gt_one_iff {x v : E} {R : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) :
    1 < dist x v ↔ ⟪x, v⟫ < R ^ 2 - 1 / 2 := by
  rw [dist_eq_norm]
  have h := sphere_chord_sq hx hv
  have hn := norm_nonneg (x - v)
  constructor <;> intro h' <;> nlinarith

/-- The specified radial centre really belongs to the slicing hyperplane. -/
theorem figureCenter_mem_hyperplane {v : E} {R : ℝ}
    (hv : ‖v‖ = R) (hR : R ≠ 0) :
    figureCenter v R ∈ figureHyperplane v R := by
  change ⟪(1 - 1 / (2 * R ^ 2)) • v, v⟫ = R ^ 2 - 1 / 2
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
  field_simp
  ring

/-- Squared circumradius of a spherical unit-distance vertex figure. -/
theorem figure_radius_sq {x v : E} {R : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) (hR : R ≠ 0)
    (hunit : dist x v = 1) :
    ‖x - figureCenter v R‖ ^ 2 = 1 - 1 / (4 * R ^ 2) := by
  have hi := (unit_distance_iff_hyperplane hx hv).mp hunit
  change ⟪x, v⟫ = R ^ 2 - 1 / 2 at hi
  simp only [figureCenter, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, hx, hv, hi]
  field_simp
  ring

/-- The nonnegative square root is the actual vertex-figure radius. -/
theorem figure_radius {x v : E} {R : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) (hR : R ≠ 0)
    (hunit : dist x v = 1) :
    dist x (figureCenter v R) = Real.sqrt (1 - 1 / (4 * R ^ 2)) := by
  rw [dist_eq_norm, ← figure_radius_sq hx hv hR hunit, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- Translation of the radius formula, applicable inside a facet with its own centre. -/
theorem translated_figure_radius {x v c : E} {R : ℝ}
    (hx : dist x c = R) (hv : dist v c = R) (hR : R ≠ 0)
    (hunit : dist x v = 1) :
    dist x (c + figureCenter (v - c) R) =
      Real.sqrt (1 - 1 / (4 * R ^ 2)) := by
  have hu : dist (x - c) (v - c) = 1 := by
    simpa only [dist_sub_right] using hunit
  have h := figure_radius (x := x - c) (v := v - c)
    (by simpa only [dist_eq_norm] using hx)
    (by simpa only [dist_eq_norm] using hv) hR hu
  rw [dist_eq_norm] at h ⊢
  convert h using 1
  congr 1
  abel

/-- Pythagoras for a spherical section whose centre is an orthogonal projection.
The orthogonality hypothesis expresses precisely the projection property needed
for the final facet-distance computation in `lem:vf`. -/
theorem orthogonal_section_distance {x o c : E} {r s : ℝ}
    (hx : dist x o = r) (hxc : dist x c = s)
    (horth : ⟪x - c, c - o⟫ = 0) :
    dist c o = Real.sqrt (r ^ 2 - s ^ 2) := by
  have hdecomp : x - o = (x - c) + (c - o) := by abel
  have hp : r ^ 2 = s ^ 2 + ‖c - o‖ ^ 2 := by
    rw [← hx, ← hxc, dist_eq_norm, dist_eq_norm, hdecomp,
      norm_add_sq_real, horth]
    ring
  rw [dist_eq_norm]
  have hs : r ^ 2 - s ^ 2 = ‖c - o‖ ^ 2 := by linarith
  rw [hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Metric part of the vertex-figure lemma for a finite spherical configuration.
The separation hypothesis is the conclusion of the paper's separation lemma;
no transitivity or dimension assumptions are needed for these formulas. -/
theorem finite_vertex_figure_formulas {S : Finset E} {v : E} {R : ℝ}
    (hvS : v ∈ S) (hS : ∀ x ∈ S, ‖x‖ = R) (hR : R ≠ 0)
    (hsep : ∀ x ∈ S, x ≠ v → 1 ≤ dist x v) :
    figureCenter v R ∈ figureHyperplane v R ∧
      ∀ x ∈ S,
        (dist x v = 1 ↔ x ∈ figureHyperplane v R) ∧
        (dist x v = 1 →
          dist x (figureCenter v R) = Real.sqrt (1 - 1 / (4 * R ^ 2))) ∧
        (x ≠ v → dist x v ≠ 1 → ⟪x, v⟫ < R ^ 2 - 1 / 2) := by
  refine ⟨figureCenter_mem_hyperplane (hS v hvS) hR, ?_⟩
  intro x hxS
  refine ⟨unit_distance_iff_hyperplane (hS x hxS) (hS v hvS),
    figure_radius (hS x hxS) (hS v hvS) hR, ?_⟩
  intro hxv hdist
  apply (distance_gt_one_iff (hS x hxS) (hS v hvS)).mp
  exact lt_of_le_of_ne (hsep x hxS hxv) (Ne.symm hdist)

/-- A translated vertex figure is orthogonal to its radial axis. -/
theorem translated_figure_axis_orthogonal {x v c : E} {S : ℝ}
    (hx : dist x c = S) (hv : dist v c = S) (hS : S ≠ 0)
    (hunit : dist x v = 1) :
    ⟪x - (c + figureCenter (v - c) S), v - c⟫ = 0 := by
  have hxn : ‖x - c‖ = S := by simpa only [dist_eq_norm] using hx
  have hvn : ‖v - c‖ = S := by simpa only [dist_eq_norm] using hv
  have hu : dist (x - c) (v - c) = 1 := by
    simpa only [dist_sub_right] using hunit
  have hi := (unit_distance_iff_hyperplane hxn hvn).mp hu
  have hc := figureCenter_mem_hyperplane hvn hS
  change ⟪x - c, v - c⟫ = S ^ 2 - 1 / 2 at hi
  change ⟪figureCenter (v - c) S, v - c⟫ = S ^ 2 - 1 / 2 at hc
  have heq : x - (c + figureCenter (v - c) S) =
      (x - c) - figureCenter (v - c) S := by abel
  rw [heq, inner_sub_left, hi, hc, sub_self]

/-- Facet vertex-figure projection from the original facet geometry. The original
facet centre `c` is orthogonal to the displacement vectors in its affine plane;
this implies that the two vertex-figure centres differ orthogonally to the
translated vertex figure. No orthogonality of those new centres is assumed. -/
theorem facet_figure_centres_orthogonal {x v c : E} {R S : ℝ}
    (hx : dist x c = S) (hv : dist v c = S) (hS : S ≠ 0)
    (hunit : dist x v = 1)
    (hxc : ⟪x - c, c⟫ = 0) (hvc : ⟪v - c, c⟫ = 0) :
    ⟪x - (c + figureCenter (v - c) S),
      (c + figureCenter (v - c) S) - figureCenter v R⟫ = 0 := by
  have haxis := translated_figure_axis_orthogonal hx hv hS hunit
  have hcenter : ⟪x - (c + figureCenter (v - c) S), c⟫ = 0 := by
    have heq : x - (c + figureCenter (v - c) S) =
        (x - c) - figureCenter (v - c) S := by abel
    rw [heq, inner_sub_left]
    simp only [figureCenter, real_inner_smul_left, hxc, hvc, mul_zero, sub_zero]
  have hdecomp : (c + figureCenter (v - c) S) - figureCenter v R =
      (1 - (1 - 1 / (2 * R ^ 2))) • c +
      ((1 - 1 / (2 * S ^ 2)) - (1 - 1 / (2 * R ^ 2))) • (v - c) := by
    simp only [figureCenter]
    module
  rw [hdecomp, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hcenter, haxis, mul_zero, mul_zero, zero_add]

/-- Distance between the whole-polytope and facet vertex-figure centres. Here the
hypotheses describe two original circumspheres and the projection property of
the original facet centre; the projection property of the new centres is derived.
The two inner square roots are precisely `r` and `r_K` in `lem:vf`. -/
theorem facet_figure_centres_point_distance {x v c : E} {R S : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) (hR : R ≠ 0)
    (hxS : dist x c = S) (hvS : dist v c = S) (hS : S ≠ 0)
    (hunit : dist x v = 1)
    (hxc : ⟪x - c, c⟫ = 0) (hvc : ⟪v - c, c⟫ = 0) :
    dist (c + figureCenter (v - c) S) (figureCenter v R) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * S ^ 2))) ^ 2) := by
  exact orthogonal_section_distance (figure_radius hx hv hR hunit)
    (translated_figure_radius hxS hvS hS hunit)
    (facet_figure_centres_orthogonal hxS hvS hS hunit hxc hvc)

/-- The affine plane of a facet's vertex figure, centred at the computed
facet-figure centre. Its normal space is generated by the original facet
normal and the radial direction within that facet. -/
noncomputable def facetFigurePlane (v c : E) (S : ℝ) : AffineSubspace ℝ E :=
  AffineSubspace.mk' (c + figureCenter (v - c) S)
    (Submodule.span ℝ ({c, v - c} : Set E))ᗮ

/-- The computed facet centre lies in the actual intersection of the global
slicing hyperplane with the original facet's affine hyperplane. -/
theorem facet_figure_center_levels {v c : E} {R S : ℝ}
    (hv : ‖v‖ = R) (hvS : dist v c = S) (hS : S ≠ 0)
    (hvc : ⟪v - c, c⟫ = 0) :
    c + figureCenter (v - c) S ∈ figureHyperplane v R ∧
    ⟪c + figureCenter (v - c) S, c⟫ = ‖c‖ ^ 2 := by
  have hvn : ‖v - c‖ = S := by simpa [dist_eq_norm] using hvS
  have hcc : ⟪c, c⟫ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hcv : ⟪c, v - c⟫ = 0 := by rwa [real_inner_comm]
  have hdecomp : R ^ 2 = S ^ 2 + ‖c‖ ^ 2 := by
    have h := norm_add_sq_real (v - c) c
    simp only [sub_add_cancel, hv, hvn, hvc] at h
    linarith
  have hlevel := figureCenter_mem_hyperplane hvn hS
  change ⟪figureCenter (v - c) S, v - c⟫ = S ^ 2 - 1 / 2 at hlevel
  have hc : ⟪c + figureCenter (v - c) S, c⟫ = ‖c‖ ^ 2 := by
    simp [figureCenter, inner_add_left, real_inner_smul_left, hvc, hcc]
  refine ⟨?_, hc⟩
  change ⟪c + figureCenter (v - c) S, v⟫ = R ^ 2 - 1 / 2
  calc
    _ = ⟪c + figureCenter (v - c) S, (v - c) + c⟫ := by rw [sub_add_cancel]
    _ = R ^ 2 - 1 / 2 := by rw [inner_add_right, hc, inner_add_left, hcv, hlevel]; linarith

/-- This is the actual facet-section hyperplane, not just a chosen point:
it is the intersection of the two original affine equations. -/
theorem facetFigurePlane_eq {v c : E} {R S : ℝ}
    (hv : ‖v‖ = R) (hvS : dist v c = S) (hS : S ≠ 0)
    (hvc : ⟪v - c, c⟫ = 0) :
    (facetFigurePlane v c S : Set E) =
      figureHyperplane v R ∩ {y | ⟪y - c, c⟫ = 0} := by
  obtain ⟨hwH, hwc⟩ := facet_figure_center_levels hv hvS hS hvc
  change ⟪c + figureCenter (v - c) S, v⟫ = R ^ 2 - 1 / 2 at hwH
  ext y
  change y - (c + figureCenter (v - c) S) ∈
      (Submodule.span ℝ ({c, v - c} : Set E))ᗮ ↔ _
  rw [Submodule.span_insert, ← Submodule.inf_orthogonal]
  simp only [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_left,
    Set.mem_inter_iff, figureHyperplane, Set.mem_setOf_eq]
  simp only [inner_sub_left, inner_sub_right, hwH, hwc, real_inner_self_eq_norm_sq]
  constructor
  · rintro ⟨hc, hv⟩
    constructor <;> linarith
  · rintro ⟨hv, hc⟩
    constructor <;> linarith

/-- The facet-section plane has codimension two in the ambient space,
hence codimension one inside the vertex-figure hyperplane. -/
theorem facetFigurePlane_dimension [FiniteDimensional ℝ E]
    {v c : E} {S : ℝ} (hc : c ≠ 0) (hvS : dist v c = S) (hS : S ≠ 0)
    (hvc : ⟪v - c, c⟫ = 0) :
    Module.finrank ℝ (facetFigurePlane v c S).direction + 2 = Module.finrank ℝ E := by
  have hv : v - c ≠ 0 := by
    intro h
    apply hS
    rw [← hvS, dist_eq_norm, h, norm_zero]
  have hcv : ⟪c, v - c⟫ = 0 := by rwa [real_inner_comm]
  have hlin : LinearIndependent ℝ ![c, v - c] :=
    linearIndependent_of_ne_zero_of_inner_eq_zero
      (by intro i; fin_cases i; exact hc; exact hv)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  have hd : Module.finrank ℝ (Submodule.span ℝ ({c, v - c} : Set E)) = 2 := by
    have hrange : Set.range ![c, v - c] = ({c, v - c} : Set E) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hdim := finrank_span_eq_card hlin
    change Module.finrank ℝ (Submodule.span ℝ (Set.range ![c, v - c])) = 2 at hdim
    rw [hrange] at hdim
    exact hdim
  have h := (Submodule.span ℝ ({c, v - c} : Set E)).finrank_add_finrank_orthogonal
  unfold facetFigurePlane
  rw [AffineSubspace.direction_mk']
  rw [hd] at h
  omega

/-- Full facet-section distance assertion: the constructed plane is the
intersection of the original facet plane with H, has the expected dimension,
and the nested square root is the distance to that plane. The original facet
centre is nonzero because its supporting hyperplane misses the interior origin. -/
theorem facet_figure_centres_distance [FiniteDimensional ℝ E]
    {x v c : E} {R S : ℝ}
    (hx : ‖x‖ = R) (hv : ‖v‖ = R) (hR : R ≠ 0)
    (hxS : dist x c = S) (hvS : dist v c = S) (hS : S ≠ 0)
    (hunit : dist x v = 1)
    (hxc : ⟪x - c, c⟫ = 0) (hvc : ⟪v - c, c⟫ = 0) (hc : c ≠ 0) :
    (facetFigurePlane v c S : Set E) =
        figureHyperplane v R ∩ {y | ⟪y - c, c⟫ = 0} ∧
    Module.finrank ℝ (facetFigurePlane v c S).direction + 2 = Module.finrank ℝ E ∧
    c + figureCenter (v - c) S ∈ facetFigurePlane v c S ∧
    Metric.infDist (figureCenter v R) (facetFigurePlane v c S : Set E) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * S ^ 2))) ^ 2) := by
  let w := c + figureCenter (v - c) S
  let o := figureCenter v R
  have hw : w ∈ facetFigurePlane v c S := AffineSubspace.self_mem_mk' _ _
  have hnormal : w - o ∈ Submodule.span ℝ ({c, v - c} : Set E) := by
    have heq : w - o =
        (1 - (1 - 1 / (2 * R ^ 2))) • c +
        ((1 - 1 / (2 * S ^ 2)) - (1 - 1 / (2 * R ^ 2))) • (v - c) := by
      dsimp [w, o, figureCenter]
      module
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hdist : Metric.infDist o (facetFigurePlane v c S : Set E) = dist w o := by
    apply le_antisymm
    · simpa [dist_comm] using Metric.infDist_le_dist_of_mem hw (x := o)
    · apply (Metric.le_infDist ⟨w, hw⟩).mpr
      intro y hy
      have hyorth : y - w ∈ (Submodule.span ℝ ({c, v - c} : Set E))ᗮ := hy
      have hi : ⟪y - w, w - o⟫ = 0 :=
        Submodule.inner_left_of_mem_orthogonal hnormal hyorth
      have hn := norm_add_sq_real (y - w) (w - o)
      have heq : y - w + (w - o) = y - o := by abel
      rw [heq, hi] at hn
      rw [dist_eq_norm, dist_comm o y, dist_eq_norm]
      nlinarith [sq_nonneg ‖y - w‖, norm_nonneg (y - o), norm_nonneg (w - o)]
  refine ⟨facetFigurePlane_eq hv hvS hS hvc,
    facetFigurePlane_dimension hc hvS hS hvc, hw, ?_⟩
  exact hdist.trans (facet_figure_centres_point_distance hx hv hR hxS hvS hS hunit hxc hvc)

end Uniform5
