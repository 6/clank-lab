import Uniform5.RaySection
import Uniform5.Formulas
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Set
open scoped RealInnerProductSpace

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [DecidableEq E]

/-- The vertex-figure level set, packaged as an affine subspace. -/
noncomputable def figureAffineHyperplane (v : E) (R : ℝ) : AffineSubspace ℝ E where
  carrier := figureHyperplane v R
  smul_vsub_vadd_mem := by
    intro a x y z hx hy hz
    change ⟪a • (x - y) + z, v⟫ = R ^ 2 - 1 / 2
    change ⟪x, v⟫ = R ^ 2 - 1 / 2 at hx
    change ⟪y, v⟫ = R ^ 2 - 1 / 2 at hy
    change ⟪z, v⟫ = R ^ 2 - 1 / 2 at hz
    simp [inner_add_left, real_inner_smul_left, inner_sub_left, hx, hy, hz]

/-- Intersection of the ray from `v` through `x` with the vertex-figure plane. -/
noncomputable def sphericalRayPoint (v x : E) (R : ℝ) : E :=
  v + (2 * (R ^ 2 - ⟪x, v⟫))⁻¹ • (x - v)

/-- The normalized ray is in the section, and the original vertex is a positive
multiple along this ray. Separation ensures that the intersection is on the segment. -/
theorem sphericalRayPoint_data (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V)
    (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hsep : ∀ x ∈ V, x ≠ v → 1 ≤ dist x v)
    {x : E} (hx : x ∈ V.erase v) :
    sphericalRayPoint v x R ∈ figureHyperplane v R ∧
    sphericalRayPoint v x R ∈ convexHull ℝ (V : Set E) ∧
    ∃ a : ℝ, 0 < a ∧ x = v + a • (sphericalRayPoint v x R - v) := by
  let a := 2 * (R ^ 2 - ⟪x, v⟫)
  have hxs := hsphere x (Finset.mem_erase.mp hx).2
  have hvs := hsphere v hv
  have hd := hsep x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
  have hch := sphere_chord_sq hxs hvs
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [dist_eq_norm] at hd
    nlinarith
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hq : sphericalRayPoint v x R ∈ figureHyperplane v R := by
    change ⟪v + a⁻¹ • (x - v), v⟫ = R ^ 2 - 1 / 2
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, hvs]
    have haeq : a = 2 * (R ^ 2 - ⟪x, v⟫) := rfl
    field_simp
    nlinarith
  refine ⟨hq, ?_, a, hap, ?_⟩
  · have ht0 : 0 ≤ a⁻¹ := inv_nonneg.mpr hap.le
    have ht1 : a⁻¹ ≤ 1 := (inv_le_one₀ hap).mpr ha
    have hcomb := (convex_convexHull ℝ (V : Set E))
      (subset_convexHull ℝ _ hv) (subset_convexHull ℝ _ (Finset.mem_erase.mp hx).2)
      (sub_nonneg.mpr ht1) ht0 (show (1 - a⁻¹) + a⁻¹ = 1 by ring)
    convert hcomb using 1
    dsimp [sphericalRayPoint, a]
    module
  · change x = v + a • (v + a⁻¹ • (x - v) - v)
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hap.ne', one_smul]
    abel

/-- A ray from a point of a sphere meets that sphere at at most one further
point. The transverse level fixes the ray's orientation and scale. -/
theorem sphericalRayPoint_injOn (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V)
    (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hsep : ∀ x ∈ V, x ≠ v → 1 ≤ dist x v) :
    Set.InjOn (fun x => sphericalRayPoint v x R) (↑(V.erase v) : Set E) := by
  intro x hx z hz heq
  obtain ⟨hq, _, a, ha, hxa⟩ := sphericalRayPoint_data V hv hsphere hsep hx
  obtain ⟨_, _, d, hd, hzd⟩ := sphericalRayPoint_data V hv hsphere hsep hz
  change sphericalRayPoint v x R = sphericalRayPoint v z R at heq
  rw [← heq] at hzd
  let w := sphericalRayPoint v x R - v
  have hinner : ⟪w, v⟫ = -(1 / 2 : ℝ) := by
    change ⟪sphericalRayPoint v x R, v⟫ = R ^ 2 - 1 / 2 at hq
    dsimp [w]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hsphere v hv]
    linarith
  have hnorm (t : ℝ) : ‖v + t • w‖ ^ 2 = R ^ 2 - t + t ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, real_inner_comm w v, hinner, hsphere v hv]
    ring
  have hxa' : x = v + a • w := hxa
  have hzd' : z = v + d • w := hzd
  have hsa : ‖x‖ ^ 2 = R ^ 2 := by rw [hsphere x (Finset.mem_erase.mp hx).2]
  have hsd : ‖z‖ ^ 2 = R ^ 2 := by rw [hsphere z (Finset.mem_erase.mp hz).2]
  rw [hxa', hnorm] at hsa
  rw [hzd', hnorm] at hsd
  have hna : a * ‖w‖ ^ 2 = 1 := by
    have hh : a * (a * ‖w‖ ^ 2 - 1) = 0 := by nlinarith
    have := (mul_eq_zero.mp hh).resolve_left ha.ne'
    linarith
  have hnd : d * ‖w‖ ^ 2 = 1 := by
    have hh : d * (d * ‖w‖ ^ 2 - 1) = 0 := by nlinarith
    have := (mul_eq_zero.mp hh).resolve_left hd.ne'
    linarith
  have hnormne : ‖w‖ ^ 2 ≠ 0 := by intro hh; rw [hh, mul_zero] at hna; norm_num at hna
  have had : a = d := mul_right_cancel₀ hnormne (hna.trans hnd.symm)
  rw [hxa', hzd', had]

/-- General section identity in the unit-edge cospherical setting. This proves
the finite tangent-cone step using exposed normalized rays. -/
theorem unit_edge_section_eq_neighborHull (V : Finset E) {v : E} {R : ℝ}
    (hv : v ∈ V) (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    convexHull ℝ (V : Set E) ∩ figureHyperplane v R =
      convexHull ℝ {x : E | IsEdge V v x} := by
  have hsq : ∀ x ∈ V, ‖x - 0‖ ^ 2 = R ^ 2 := by
    intro x hx
    simp [hsphere x hx]
  have hsep : ∀ x ∈ V, x ≠ v → 1 ≤ dist x v := by
    intro x hx hxv
    exact unit_edges_separated V hsq hunit hx hv hxv
  let q := fun x => sphericalRayPoint v x R
  let L := innerSL ℝ v
  let b := R ^ 2 - 1 / 2
  have hLv : L v = R ^ 2 := by simp only [L, innerSL_apply, real_inner_self_eq_norm_sq, hsphere v hv]
  have hb : b < L v := by rw [hLv]; dsimp [b]; linarith
  have hlev : ∀ x ∈ V.erase v, L (q x) = b := by
    intro x hx
    have hh := (sphericalRayPoint_data V hv hsphere hsep hx).1
    simpa only [q, L, b, figureHyperplane, mem_setOf_eq, innerSL_apply,
      real_inner_comm v] using hh
  have hmem : ∀ x ∈ V.erase v, q x ∈ convexHull ℝ (V : Set E) := by
    intro x hx
    exact (sphericalRayPoint_data V hv hsphere hsep hx).2.1
  have hrep : ∀ x ∈ V.erase v, ∃ a : ℝ, 0 < a ∧ x = v + a • (q x - v) := by
    intro x hx
    exact (sphericalRayPoint_data V hv hsphere hsep hx).2.2
  have hslic := finite_section_eq_rayHull V L hb q hlev hmem hrep
  have hsets : convexHull ℝ (V : Set E) ∩ figureHyperplane v R =
      convexHull ℝ (q '' (↑(V.erase v) : Set E)) := by
    convert hslic using 1
    ext y
    simp only [mem_inter_iff, mem_setOf_eq, figureHyperplane, L, b, innerSL_apply]
    rw [real_inner_comm v y]
  rw [hsets]
  apply le_antisymm
  · let Q := (V.erase v).image q
    have hQ : (Q : Set E) = q '' (↑(V.erase v) : Set E) := Finset.coe_image
    rw [← hQ, ← finite_convexHull_exposedPoints Q]
    apply convexHull_mono
    intro y hy
    have hyQ : y ∈ (Q : Set E) :=
      extremePoints_convexHull_subset (exposedPoints_subset_extremePoints hy)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyQ
    have hex : IsEdge V v x := ray_exposedPoint_isEdge V hv L hb q hlev hrep
      (sphericalRayPoint_injOn V hv hsphere hsep) hx (by simpa only [hQ] using hy)
    have hdist := hunit v x hex
    have hch := sphere_chord_sq (hsphere x (Finset.mem_erase.mp hx).2) (hsphere v hv)
    rw [dist_comm, dist_eq_norm] at hdist
    have ha : 2 * (R ^ 2 - ⟪x, v⟫) = 1 := by nlinarith
    have hqx : q x = x := by
      change v + (2 * (R ^ 2 - ⟪x, v⟫))⁻¹ • (x - v) = x
      rw [ha]
      simp
    change IsEdge V v (q x)
    rw [hqx]
    exact hex
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    have hxv := hx.2.2.1.symm
    have hxe : x ∈ V.erase v := Finset.mem_erase.mpr ⟨hxv, hx.2.1⟩
    have hdist := hunit v x hx
    have hch := sphere_chord_sq (hsphere x hx.2.1) (hsphere v hv)
    rw [dist_comm, dist_eq_norm] at hdist
    have ha : 2 * (R ^ 2 - ⟪x, v⟫) = 1 := by nlinarith
    have hqx : q x = x := by
      change v + (2 * (R ^ 2 - ⟪x, v⟫))⁻¹ • (x - v) = x
      rw [ha]
      simp
    exact subset_convexHull ℝ _ ⟨x, hxe, hqx⟩

end Uniform5
