import Uniform5.CompositionFigure
import Uniform5.VertexFigure

/-!
# Metric vertex-figure formulas for actual unit-uniform five-polytopes

The center is the arithmetic centroid of actual vertices. Centeredness,
cosphericity, positive radius and full affine span are derived from the
concrete uniformity definition before using the earlier metric lemmas.
-/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal hyperplane equation of the actual translated section. -/
theorem vertexFigure_eq_inner_section (P : Set E) (v c : E) (R : ℝ)
    (hv : ‖v - c‖ ^ 2 = R ^ 2) :
    vertexFigure P v c = {x ∈ P | ⟪x - c, v - c⟫ = R ^ 2 - 1 / 2} := by
  have heq (x : E) : sphereHeight (c - v) (x - v) =
      2 * (R ^ 2 - ⟪x - c, v - c⟫) := by
    have hcv : c - v = -(v - c) := by abel
    have hxv : x - v = (x - c) - (v - c) := by abel
    change 2 * ⟪c - v, x - v⟫ = _
    rw [hcv, hxv, inner_neg_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hv, real_inner_comm (v - c) (x - c)]
    ring
  ext x
  simp only [vertexFigure, Set.mem_setOf_eq, heq]
  constructor
  · rintro ⟨hx, hh⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hh⟩
    exact ⟨hx, by linarith⟩

theorem vertexFigure_zero_center_eq (P : Set E) (v : E) (R : ℝ)
    (hv : ‖v‖ = R) :
    vertexFigure P v 0 = P ∩ figureHyperplane v R := by
  simpa only [sub_zero, figureHyperplane, Set.inter_setOf_eq_sep] using
    vertexFigure_eq_inner_section P v 0 R (by simp only [sub_zero, hv])

/-- The true vertex set of a uniform five-polytope has more than one point. -/
theorem unitUniform5_vertices_card_gt_one {P : Set (Space 5)} (hP : UnitUniform 5 P) :
    1 < (vertices P (uniform_finitePolytope hP.1)).card := by
  classical
  let V := vertices P (uniform_finitePolytope hP.1)
  have hVne : V.Nonempty := vertices_nonempty _
  change 1 < V.card
  by_contra hcard
  have heq : V.card = 1 := by have hh := Finset.card_pos.mpr hVne; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp heq
  have hHull := convexHull_vertices (uniform_finitePolytope hP.1)
  change convexHull ℝ (V : Set (Space 5)) = P at hHull
  rw [hv] at hHull
  simp only [Finset.coe_singleton, convexHull_singleton] at hHull
  exact not_uniform5_singleton v (hHull ▸ hP.1)

/-- Translating by the actual vertex centroid discharges the zero-mean
premise of the earlier vertex-figure interior theorem. -/
theorem unitUniform5_centroid_figureCenter_mem_intrinsicInterior
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (R : ℝ) (hR : 0 < R)
    (hsphere : ∀ x ∈ P.extremePoints ℝ,
      ‖x - vertexCentroid (vertices P (uniform_finitePolytope hP.1))‖ ^ 2 = R ^ 2)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    c + figureCenter (v - c) R ∈ intrinsicInterior ℝ (vertexFigure P v c) := by
  classical
  let V := vertices P (uniform_finitePolytope hP.1)
  let c := vertexCentroid V
  let g := (AffineIsometryEquiv.vaddConst ℝ c).symm
  let W := V.image g
  have hg (x : Space 5) : g x = x - c := rfl
  have hV : convexHull ℝ (V : Set (Space 5)) = P := convexHull_vertices _
  have hW : convexHull ℝ (W : Set (Space 5)) = g '' P := by
    rw [← hV]
    simpa only [W, Finset.coe_image] using
      (g.toAffineMap.image_convexHull (V : Set (Space 5))).symm
  have hvV : v ∈ V := (mem_vertices _ v).mpr hv
  have hvW : g v ∈ W := Finset.mem_image.mpr ⟨v, hvV, rfl⟩
  have hcard : 1 < W.card := by
    rw [Finset.card_image_of_injective V g.injective]
    exact unitUniform5_vertices_card_gt_one hP
  have hsum : ∑ x ∈ W, x = 0 := by
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    simp only [hg]
    exact sum_sub_vertexCentroid V (vertices_nonempty _)
  have hs : ∀ x ∈ W, ‖x‖ = R := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := hsphere y ((mem_vertices _ y).mp hy)
    change ‖y - c‖ ^ 2 = R ^ 2 at hh
    exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp hh
  have hspan : affineSpan ℝ (W : Set (Space 5)) = ⊤ := by
    rw [← affineSpan_convexHull, hW]
    exact uniform5_affineSpan_eq_top (uniform_image g hP.1)
  have hsep : ∀ x ∈ W, x ≠ g v → 1 ≤ dist x (g v) := by
    rintro x hx hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [g.dist_map]
    exact unitUniform_separated hP ((mem_vertices _ y).mp hy) hv
      (fun heq => hne (congrArg g heq))
  have hint := figureCenter_mem_intrinsicInterior W hvW hcard hspan hsum hs hR.ne' hsep
  have hsection : convexHull ℝ (W : Set (Space 5)) ∩ figureHyperplane (g v) R =
      g '' vertexFigure P v c := by
    rw [hW, ← vertexFigure_zero_center_eq _ _ _ (hs _ hvW), vertexFigure_image]
    have hgc : g c = 0 := by rw [hg, sub_self]
    rw [hgc]
  rw [hsection] at hint
  have hint' : figureCenter (g v) R ∈ g '' intrinsicInterior ℝ (vertexFigure P v c) := by
    have hi := g.toAffineIsometry.image_intrinsicInterior (vertexFigure P v c)
    change intrinsicInterior ℝ (g '' vertexFigure P v c) =
      g '' intrinsicInterior ℝ (vertexFigure P v c) at hi
    rwa [hi] at hint
  obtain ⟨x, hx, hxeq⟩ := hint'
  have hxc : x = c + figureCenter (v - c) R := by
    rw [hg] at hxeq
    rw [hg] at hxeq
    exact (sub_eq_iff_eq_add.mp hxeq).trans (add_comm _ _)
  simpa only [hxc] using hx

/-- The actual arithmetic vertex centroid is the sphere center, with
positive radius derived from the dimension-five uniformity assumption. -/
theorem unitUniform5_centroid_sphere {P : Set (Space 5)} (hP : UnitUniform 5 P) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ P.extremePoints ℝ, dist x c = R := by
  obtain ⟨R, hR, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hpos := uniform_sphere_radius_pos hP.1 hR hs
  refine ⟨R, hpos, ?_⟩
  intro x hx
  rw [dist_eq_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (hs x hx)

/-- A nonzero level hyperplane is exhausted by a subset with the same
affine codimension one. -/
theorem affineSpan_eq_level_of_codimension_one [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (hL : L ≠ 0) (S : Set E) (hne : S.Nonempty) (b : ℝ)
    (hlevel : ∀ x ∈ S, L x = b)
    (hdim : affineDimension S + 1 = Module.finrank ℝ E) :
    (affineSpan ℝ S : Set E) = {x | L x = b} := by
  have hdir : (affineSpan ℝ S).direction = LinearMap.ker L := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [direction_affineSpan]
      exact vectorSpan_le_ker_of_level L S b hlevel
    · have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hL
      unfold affineDimension Uniform5.affineDimension at hdim
      omega
  obtain ⟨a, ha⟩ := hne
  have ha' : a ∈ affineSpan ℝ S := subset_affineSpan ℝ S ha
  ext x
  have hm := AffineSubspace.vadd_mem_iff_mem_direction (x - a) ha'
  simpa only [vadd_eq_add, sub_add_cancel, hdir, LinearMap.mem_ker, map_sub,
    hlevel a ha, sub_eq_zero, Set.mem_setOf_eq] using hm

/-- The actual figure spans its entire geometric slicing plane. -/
theorem unitUniform5_vertexFigure_affineSpan {P : Set (Space 5)} (hP : UnitUniform 5 P)
    (R : ℝ) (hR : 0 < R)
    (hsphere : ∀ x ∈ P.extremePoints ℝ,
      ‖x - vertexCentroid (vertices P (uniform_finitePolytope hP.1))‖ ^ 2 = R ^ 2)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    (affineSpan ℝ (vertexFigure P v c) : Set (Space 5)) =
      {x | ⟪x - c, v - c⟫ = R ^ 2 - 1 / 2} := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let L := (innerSL ℝ (v - c)).toLinearMap
  have hL : L ≠ 0 := by
    intro hh
    have hh' := congrArg (fun f : Space 5 →ₗ[ℝ] ℝ => f (v - c)) hh
    change ⟪v - c, v - c⟫ = 0 at hh'
    rw [real_inner_self_eq_norm_sq, hsphere v hv] at hh'
    nlinarith
  have hlevel (x : Space 5) : L x = L c + (R ^ 2 - 1 / 2) ↔
      ⟪x - c, v - c⟫ = R ^ 2 - 1 / 2 := by
    change ⟪v - c, x⟫ = ⟪v - c, c⟫ + _ ↔ _
    rw [real_inner_comm (v - c) (x - c), inner_sub_right]
    constructor <;> intro hh <;> linarith
  have hinterior := unitUniform5_centroid_figureCenter_mem_intrinsicInterior hP R hR hsphere hv
  have hne : (vertexFigure P v c).Nonempty :=
    ⟨c + figureCenter (v - c) R, intrinsicInterior_subset hinterior⟩
  have hdim := finitePolytope_unit_vertexFigure_dimension (uniform_finitePolytope hP.1)
    hv c R hsphere hP.2 (by simpa using uniform_dimension hP.1) (by simp)
  have hh := affineSpan_eq_level_of_codimension_one L hL (vertexFigure P v c) hne
    (L c + (R ^ 2 - 1 / 2)) (fun x hx => (hlevel x).mpr (by
      rw [vertexFigure_eq_inner_section P v c R (hsphere v hv)] at hx
      exact hx.2)) hdim
  change (affineSpan ℝ (vertexFigure P v c) : Set (Space 5)) = _
  rw [hh]
  exact Set.ext hlevel

/-- The metric and relative-interior conclusions of the paper's
vertex-figure lemma, now quantified over actual unit-uniform five-polytopes.
No centeredness, sphere, mean, full-span or neighbor-encoding input remains. -/
theorem unitUniform5_vertexFigure_metric {P : Set (Space 5)} (hP : UnitUniform 5 P) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    ∃ R : ℝ, 0 < R ∧ (∀ x ∈ P.extremePoints ℝ, dist x c = R) ∧
      ∀ v ∈ P.extremePoints ℝ,
        vertexFigure P v c = {x ∈ P | ⟪x - c, v - c⟫ = R ^ 2 - 1 / 2} ∧
        (affineSpan ℝ (vertexFigure P v c) : Set (Space 5)) =
          {x | ⟪x - c, v - c⟫ = R ^ 2 - 1 / 2} ∧
        c + figureCenter (v - c) R ∈ intrinsicInterior ℝ (vertexFigure P v c) ∧
        ∀ x ∈ (vertexFigure P v c).extremePoints ℝ,
          dist x (c + figureCenter (v - c) R) = Real.sqrt (1 - 1 / (4 * R ^ 2)) := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  obtain ⟨R, hR, hs⟩ := unitUniform5_centroid_sphere hP
  have hsquare : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2 := by
    intro x hx
    rw [← dist_eq_norm, hs x hx]
  refine ⟨R, hR, hs, ?_⟩
  intro v hv
  refine ⟨vertexFigure_eq_inner_section P v c R (hsquare v hv),
    unitUniform5_vertexFigure_affineSpan hP R hR hsquare hv,
    unitUniform5_centroid_figureCenter_mem_intrinsicInterior hP R hR hsquare hv, ?_⟩
  intro x hx
  rw [finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv c R hsquare hP.2] at hx
  exact translated_figure_radius (hs x hx.2.1) (hs v hv) hR.ne'
    (by rw [dist_comm]; exact hP.2 v x hx)

/-- The explicit center is on the radial axis and is perpendicular to
every displacement within the actual vertex-figure section. -/
theorem vertexFigure_axis_orthogonal {P : Set E} {v c x : E} {R : ℝ}
    (hv : ‖v - c‖ = R) (hR : R ≠ 0) (hx : x ∈ vertexFigure P v c) :
    ⟪x - (c + figureCenter (v - c) R), v - c⟫ = 0 := by
  have hsection := vertexFigure_eq_inner_section P v c R (by rw [hv])
  rw [hsection] at hx
  have hc := figureCenter_mem_hyperplane hv hR
  change ⟪figureCenter (v - c) R, v - c⟫ = R ^ 2 - 1 / 2 at hc
  have heq : x - (c + figureCenter (v - c) R) =
      (x - c) - figureCenter (v - c) R := by abel
  rw [heq, inner_sub_left, hx.2, hc, sub_self]

end Uniform5.Composition
