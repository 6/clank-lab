import Uniform5.Separation
import Uniform5.Formulas
import Uniform5.Centroid
import Uniform5.CentroidWeights
import Uniform5.Sections
import Uniform5.ConvexSection
import Uniform5.PolygonGeometry
import Uniform5.FacetGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped BigOperators RealInnerProductSpace

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The corrected two-case centroid argument of `lem:vf`.
Full-dimensionality is expressed by the affine span being the whole ambient space.
No sign assumption is imposed on the coefficient of the figure centre. -/
theorem figureCenter_mem_intrinsicInterior [FiniteDimensional ℝ E]
    (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V) (hcard : 1 < V.card)
    (hspan : affineSpan ℝ (V : Set E) = ⊤)
    (hsum : ∑ x ∈ V, x = 0) (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hR : R ≠ 0) (hsep : ∀ x ∈ V, x ≠ v → 1 ≤ dist x v) :
    figureCenter v R ∈ intrinsicInterior ℝ
      (convexHull ℝ (V : Set E) ∩ figureHyperplane v R) := by
  classical
  let a : ℝ := -1 / ((V.card : ℝ) - 1)
  let t : ℝ := 1 - 1 / (2 * R ^ 2)
  have hR2 : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  have htH := figureCenter_mem_hyperplane (hsphere v hv) hR
  have htval : t * R ^ 2 = R ^ 2 - 1 / 2 := by
    change ⟪t • v, v⟫ = R ^ 2 - 1 / 2 at htH
    simpa only [real_inner_smul_left, real_inner_self_eq_norm_sq, hsphere v hv] using htH
  have hle : ∀ x ∈ V.erase v, ⟪x, v⟫ ≤ R ^ 2 - 1 / 2 := by
    intro x hx
    have hxV := (Finset.mem_erase.mp hx).2
    have hd := hsep x hxV (Finset.mem_erase.mp hx).1
    have hsq := sphere_chord_sq (hsphere x hxV) (hsphere v hv)
    rw [dist_eq_norm] at hd
    nlinarith
  have hqHull := erasedCentroid_mem_convexHull hv hcard hsum
  have hqinner : ⟪erasedCentroid V v, v⟫ = a * R ^ 2 := by
    simp only [erasedCentroid, real_inner_smul_left, real_inner_self_eq_norm_sq, hsphere v hv]
    rfl
  by_cases hstrict : ∃ x ∈ V.erase v, ⟪x, v⟫ < R ^ 2 - 1 / 2
  · have hqstrict := erasedCentroid_inner_lt hv hcard hsum hle hstrict
    rw [hqinner] at hqstrict
    have hat : a < t := (mul_lt_mul_right hR2).mp (hqstrict.trans_eq htval.symm)
    have hneg : a < 0 := by
      dsimp [a]
      have hc : (1 : ℝ) < V.card := by exact_mod_cast hcard
      exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
    have ht : t < 1 := by
      dsimp [t]
      have hp : 0 < 1 / (2 * R ^ 2) := by positivity
      linarith
    have hzero : (0 : E) ∈ interior (convexHull ℝ (V : Set E)) := by
      have hh := zero_mem_interior_convexHull_of_sum_zero (fun x : V => (x : E))
        (by simpa [Finset.sum_attach V (fun x => x)] using hsum)
        (by simpa using interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan)
      simpa using hh
    have hq : a • v ∈ convexHull ℝ (V : Set E) :=
      convexHull_mono (by exact_mod_cast Finset.erase_subset v V) hqHull
    have hc := axial_point_mem_interior (convex_convexHull ℝ _) hzero
      (subset_convexHull ℝ _ hv) hneg hq hat ht
    exact interior_mem_intrinsicInterior_section (figureAffineHyperplane v R) hc htH
  · have heq : ∀ x ∈ V.erase v, ⟪x, v⟫ = R ^ 2 - 1 / 2 := by
      intro x hx
      exact le_antisymm (hle x hx) (not_lt.mp (fun h => hstrict ⟨x, hx, h⟩))
    have hqe := erasedCentroid_inner_eq hv hcard hsum heq
    rw [hqinner] at hqe
    have hat : a = t := mul_right_cancel₀ hR2.ne' (hqe.trans htval.symm)
    have hqc : erasedCentroid V v = figureCenter v R := by
      change a • v = t • v
      rw [hat]
    have hmean : ∑ x ∈ V.erase v, x = ((V.erase v).card : ℝ) • erasedCentroid V v := by
      rw [erasedCentroid_eq_mean hv hsum, smul_smul,
        mul_inv_cancel₀ (ne_of_gt (erased_card_pos hv hcard)), one_smul]
    have hrel := finset_mean_mem_intrinsicInterior_convexHull (V.erase v)
      (Finset.card_pos.mp (by exact_mod_cast erased_card_pos hv hcard))
      (erasedCentroid V v) hmean
    have hslice := finite_vertex_section V v (innerSL ℝ v) (R ^ 2 - 1 / 2) hv
      (by intro x hx; simpa only [innerSL_apply, real_inner_comm v] using heq x hx)
      (by simp only [innerSL_apply, real_inner_self_eq_norm_sq, hsphere v hv]; linarith)
    have hsets : convexHull ℝ (V : Set E) ∩ figureHyperplane v R =
        convexHull ℝ (V.erase v : Set E) := by
      convert hslice using 1
      ext x
      simp only [mem_inter_iff, figureHyperplane, mem_setOf_eq, innerSL_apply]
      rw [real_inner_comm v x]
    rw [hsets, ← hqc]
    exact hrel

/-- The centroid conclusion with unit edges as the input, rather than a separate
separation assumption. This is the finite-set form used by the paper. -/
theorem unit_edge_figureCenter_mem_intrinsicInterior [FiniteDimensional ℝ E]
    (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V) (hcard : 1 < V.card)
    (hspan : affineSpan ℝ (V : Set E) = ⊤)
    (hsum : ∑ x ∈ V, x = 0) (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hR : R ≠ 0) (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    figureCenter v R ∈ intrinsicInterior ℝ
      (convexHull ℝ (V : Set E) ∩ figureHyperplane v R) := by
  apply figureCenter_mem_intrinsicInterior V hv hcard hspan hsum hsphere hR
  intro x hx hxv
  exact unit_edges_separated V (c := 0) (R := R)
    (by intro y hy; simp [hsphere y hy]) hunit hx hv hxv

/-- The section has codimension one. The face-dimension theorem also covers
the degenerate zero-dimensional ambient case by natural-number truncation. -/
theorem unit_edge_section_finrank [FiniteDimensional ℝ E]
    (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V)
    (hspan : affineSpan ℝ (V : Set E) = ⊤)
    (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    Module.finrank ℝ (affineSpan ℝ
      (convexHull ℝ (V : Set E) ∩ figureHyperplane v R)).direction =
      Module.finrank ℝ E - 1 := by
  classical
  have hh := unit_edge_exposedFace_section_finrank V hv hsphere hunit
    (IsExposed.refl (convexHull ℝ (V : Set E))) (subset_convexHull ℝ _ hv)
  rw [affineSpan_convexHull, hspan, AffineSubspace.direction_top, finrank_top] at hh
  exact hh

/-- The vertex-figure lemma for a finite Euclidean hull, including ordinary
face correspondence, actual facet sections, and edges from unit regular polygons.
Centredness and cosphericity are the outputs of the paper's sphere lemma;
unit edges and full-dimensionality are its geometric input assumptions. -/
theorem euclidean_unit_edge_vertex_figure {n : ℕ}
    (V : Finset (EuclideanSpace ℝ (Fin n))) {v : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hv : v ∈ V) (hcard : 1 < V.card) (hspan : affineSpan ℝ (V : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (hsum : ∑ x ∈ V, x = 0) (hsphere : ∀ x ∈ V, ‖x‖ = R) (hR : R ≠ 0)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    (∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) ∧
    (∀ x ∈ V, IsEdge V x v ↔ x ∈ figureHyperplane v R) ∧
    (figureCenter v R ∈ figureHyperplane v R) ∧
    (∀ x ∈ V, IsEdge V x v →
      dist x (figureCenter v R) = Real.sqrt (1 - 1 / (4 * R ^ 2))) ∧
    figureCenter v R ∈ intrinsicInterior ℝ
      (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ∩ figureHyperplane v R) ∧
    (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ∩ figureHyperplane v R =
      convexHull ℝ {x | IsEdge V v x}) ∧
    Module.finrank ℝ (affineSpan ℝ
      (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ∩ figureHyperplane v R)).direction =
      n - 1 ∧
    ExposedVertexFigureCorrespondence V v R ∧
    ConvexVertexFigureCorrespondence V v R ∧
    (∀ x ∈ V, x ≠ v → ¬ IsEdge V x v → ⟪x, v⟫ < R ^ 2 - 1 / 2) ∧
    FacetSectionGeometry V v R ∧
    PolygonSectionGeometry V v R := by
  have hsq : ∀ x ∈ V, ‖x - 0‖ ^ 2 = R ^ 2 := by
    intro x hx
    simp only [sub_zero, hsphere x hx]
  refine ⟨?_, ?_, figureCenter_mem_hyperplane (hsphere v hv) hR, ?_,
    unit_edge_figureCenter_mem_intrinsicInterior V hv hcard hspan hsum hsphere hR hunit,
    unit_edge_section_eq_neighborHull V hv hsphere hunit, ?_,
    unit_edge_exposedVertexFigureCorrespondence V hv hsphere hunit,
    unit_edge_convexVertexFigureCorrespondence V hv hsphere hunit, ?_, ?_,
    unit_edge_polygonSectionGeometry V hv hsphere hunit⟩
  · intro x hx y hy hxy
    exact unit_edges_separated V hsq hunit hx hy hxy
  · intro x hx
    exact (isEdge_iff_dist_eq_one V hsq hunit hx hv).trans
      (unit_distance_iff_hyperplane (hsphere x hx) (hsphere v hv))
  · intro x hx he
    exact figure_radius (hsphere x hx) (hsphere v hv) hR (hunit x v he)
  · simpa using unit_edge_section_finrank V hv hspan hsphere hunit
  · intro x hx hxv hne
    apply (distance_gt_one_iff (hsphere x hx) (hsphere v hv)).mp
    have hle := unit_edges_separated V hsq hunit hx hv hxv
    have hdist : dist x v ≠ 1 := fun hh => hne ((isEdge_iff_dist_eq_one V hsq hunit hx hv).mpr hh)
    exact lt_of_le_of_ne hle (Ne.symm hdist)
  · apply unit_edge_facetSectionGeometry V hv hsphere hR hunit
    have hh := zero_mem_interior_convexHull_of_sum_zero (fun x : V => (x : EuclideanSpace ℝ (Fin n)))
      (by simpa [Finset.sum_attach V (fun x => x)] using hsum)
      (by simpa using interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan)
    simpa using hh

/-- Regression example for the negative coefficient highlighted by the paper:
the unit regular 5-simplex has squared radius `5/12`. -/
theorem five_simplex_center_coefficient {v : E} {R : ℝ} (hR : R ^ 2 = 5 / 12) :
    figureCenter v R = (-1 / 5 : ℝ) • v := by
  simp only [figureCenter, hR]
  norm_num

end Uniform5
