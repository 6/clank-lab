import Uniform5.CompositionFaces
import Uniform5.CompositionSymmetry
import Uniform5.CompositionRadialEdges

/-!
# Connectivity of the actual vertex-edge graph

Linear functionals attain a maximum at a vertex. The finite-ascent argument
below uses real exposed-segment edges and actual extreme points.
-/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A functional on a finite polytope has a maximizing actual vertex. -/
theorem finitePolytope_exists_extreme_max {P : Set E} (hP : FinitePolytope P)
    (L : E →L[ℝ] ℝ) :
    ∃ q ∈ P.extremePoints ℝ, ∀ x ∈ P, L x ≤ L q := by
  obtain ⟨z, hz, hmax⟩ := (finitePolytope_isCompact hP).exists_isMaxOn
    (finitePolytope_nonempty hP) L.continuous.continuousOn
  let F : Set E := {x ∈ P | ∀ y ∈ P, L y ≤ L x}
  have hF : IsExposed ℝ P F := fun _ => ⟨L, rfl⟩
  obtain ⟨q, hq⟩ := (hF.isCompact (finitePolytope_isCompact hP)).extremePoints_nonempty
    ⟨z, hz, hmax⟩
  exact ⟨q, hF.isExtreme.extremePoints_subset_extremePoints hq, hq.1.2⟩

/-- On a finite set, a strict-improvement step at every nonterminal point
produces a finite path to the terminal point. -/
theorem finite_path_of_improving {α : Type*} {S : Set α} (hS : S.Finite)
    (R : α → α → Prop) (f : α → ℝ) {x y : α} (hx : x ∈ S)
    (improve : ∀ z ∈ S, z ≠ y → ∃ w ∈ S, R z w ∧ f z < f w) :
    Relation.ReflTransGen R x y := by
  let T : Set α := {z ∈ S | Relation.ReflTransGen R x z}
  have hT : T.Finite := hS.subset (fun _ h => h.1)
  have hTne : T.Nonempty := ⟨x, hx, Relation.ReflTransGen.refl⟩
  obtain ⟨z, hz, hmax⟩ := T.exists_max_image f hT hTne
  by_cases hzy : z = y
  · simpa only [hzy] using hz.2
  · obtain ⟨w, hw, hzw, hlt⟩ := improve z hz.1 hzy
    have hwT : w ∈ T := ⟨hw, hz.2.tail hzw⟩
    exact False.elim ((not_lt_of_ge (hmax w hwT)) hlt)

/-- A functional that increases somewhere has an increasing actual edge
from the origin. The normalized tangent hull supplies that edge. -/
theorem finitePolytope_improving_edge_zero {P : Set E} (hP : FinitePolytope P)
    (hzero : (0 : E) ∈ P.extremePoints ℝ) (M : E →L[ℝ] ℝ)
    {w : E} (hw : w ∈ P.extremePoints ℝ) (hMw : 0 < M w) :
    ∃ x, Edge P 0 x ∧ 0 < M x := by
  classical
  let V := vertices P hP
  have hV : convexHull ℝ (V : Set E) = P := convexHull_vertices hP
  have hzeroV : (0 : E) ∈ V := (mem_vertices hP 0).mpr hzero
  have hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ := by
    intro x hx
    rw [hV]
    exact (mem_vertices hP x).mp hx
  obtain ⟨L, hL⟩ := finite_extreme_strict_support V (hvertices 0 hzeroV)
  have hpos : ∀ x ∈ V.erase 0, 0 < (-L) x := by
    intro x hx
    have hh := hL x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
    simpa only [map_zero, ContinuousLinearMap.neg_apply, neg_pos] using hh
  have hw0 : w ≠ 0 := by intro heq; simp [heq] at hMw
  have hwV : w ∈ V.erase 0 := Finset.mem_erase.mpr ⟨hw0, (mem_vertices hP w).mpr hw⟩
  let S := (V.erase 0).image (radialPoint (-L))
  have hS : FinitePolytope (convexHull ℝ (S : Set E)) :=
    ⟨S, ⟨radialPoint (-L) w, Finset.mem_image.mpr ⟨w, hwV, rfl⟩⟩, rfl⟩
  obtain ⟨q, hq, hmax⟩ := finitePolytope_exists_extreme_max hS M
  have hwS : radialPoint (-L) w ∈ convexHull ℝ (S : Set E) :=
    subset_convexHull ℝ (S : Set E) (Finset.mem_image.mpr ⟨w, hwV, rfl⟩)
  have hMrad : 0 < M (radialPoint (-L) w) := by
    simp only [radialPoint, map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (hpos w hwV)) hMw
  have hMq : 0 < M q := hMrad.trans_le (hmax _ hwS)
  obtain ⟨x, hx, hr, hedge⟩ := radial_extreme_isEdge V hzeroV hvertices (-L) hpos hq
  refine ⟨x, ?_, ?_⟩
  · exact (edge_iff_vertices_isEdge hP 0 x).mpr hedge
  · have hh := congrArg M (radialPoint_recover (-L) (hpos x hx).ne')
    rw [map_smul, smul_eq_mul, hr] at hh
    rw [← hh]
    exact mul_pos (hpos x hx) hMq

/-- Every nonmaximal actual vertex has an incident exposed-segment edge
along which a prescribed linear objective strictly increases. -/
theorem finitePolytope_improving_edge {P : Set E} (hP : FinitePolytope P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (M : E →L[ℝ] ℝ) (hMw : M v < M w) :
    ∃ x, Edge P v x ∧ M v < M x := by
  let t := (AffineIsometryEquiv.vaddConst ℝ v).symm
  have hzero : (0 : E) ∈ (t '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints]
    exact ⟨v, hv, by simp [t]⟩
  have hw' : t w ∈ (t '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints]
    exact ⟨w, hw, rfl⟩
  have hMw' : 0 < M (t w) := by
    change 0 < M (w - v)
    rw [map_sub]
    exact sub_pos.mpr hMw
  obtain ⟨x, hx, hMx⟩ := finitePolytope_improving_edge_zero
    (finitePolytope_image t hP) hzero M hw' hMw'
  refine ⟨t.symm x, ?_, ?_⟩
  · have hedge := edge_image t.symm hx
    rw [affineIsometry_symm_image_image] at hedge
    simpa only [t, AffineIsometryEquiv.symm_symm,
      AffineIsometryEquiv.coe_vaddConst, zero_vadd] using hedge
  · change M v < M (x + v)
    rw [map_add]
    linarith

/-- The graph on actual vertices, with actual exposed segments as edges,
is connected for every finite convex polytope. -/
theorem finitePolytope_edge_connected {P : Set E} (hP : FinitePolytope P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) :
    Relation.ReflTransGen (Edge P) v w := by
  let V := vertices P hP
  have hwV : w ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ := by
    rwa [convexHull_vertices]
  obtain ⟨L, hL⟩ := finite_extreme_strict_support V hwV
  apply finite_path_of_improving (finitePolytope_extremePoints_finite hP) (Edge P) L hv
  intro z hz hzw
  have hzw' : L z < L w := hL z ((mem_vertices hP z).mpr hz) hzw
  obtain ⟨x, hedge, hinc⟩ := finitePolytope_improving_edge hP hz hw L hzw'
  exact ⟨x, hedge.2.1, hedge, hinc⟩

/-- Connectivity applies directly to the concrete dimension-five models. -/
theorem UnitUniform5.edge_connected (P : UnitUniform5) {v w : Space 5}
    (hv : v ∈ P.val.extremePoints ℝ) (hw : w ∈ P.val.extremePoints ℝ) :
    Relation.ReflTransGen (Edge P.val) v w :=
  finitePolytope_edge_connected (uniform_finitePolytope P.property.1) hv hw

end Uniform5.Composition
