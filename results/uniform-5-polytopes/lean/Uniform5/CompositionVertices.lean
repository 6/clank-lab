import Uniform5.CompositionGeometry
import Uniform5.CompositionSphere
import Uniform5.Centroid
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology

/-!
# Actual vertices, centroid spheres, and unit-edge separation

The finite vertex set here is the set of extreme points of the geometric
polytope, not an arbitrarily labelled generating set. Compact Krein--Milman
proves that its hull is the original polytope. Thus the conclusions below
apply directly to `Uniform`, with no extra sphere or vertex-encoding premise.
-/

noncomputable section

namespace Uniform5.Composition

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite polytope is compact, including in an infinite-dimensional
ambient normed space. -/
theorem finitePolytope_isCompact {P : Set E} (hP : FinitePolytope P) :
    IsCompact P := by
  obtain ⟨V, _, rfl⟩ := hP
  exact V.finite_toSet.isCompact_convexHull

/-- The true vertex set is nonempty. -/
theorem finitePolytope_extremePoints_nonempty {P : Set E} (hP : FinitePolytope P) :
    (P.extremePoints ℝ).Nonempty :=
  (finitePolytope_isCompact hP).extremePoints_nonempty (finitePolytope_nonempty hP)

/-- The original polytope is exactly the convex hull of its extreme points.
The finite hull is closed, so the closure in Krein--Milman disappears. -/
theorem finitePolytope_eq_convexHull_extremePoints {P : Set E}
    (hP : FinitePolytope P) : P = convexHull ℝ (P.extremePoints ℝ) := by
  have hk := closure_convexHull_extremePoints (finitePolytope_isCompact hP)
    (finitePolytope_convex hP)
  rw [(finitePolytope_extremePoints_finite hP).isCompact_convexHull.isClosed.closure_eq] at hk
  exact hk.symm

/-- An affine isometry transports actual extreme points. -/
theorem affineIsometry_image_extremePoints (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    g '' P.extremePoints ℝ = (g '' P).extremePoints ℝ := by
  have forward (f : E ≃ᵃⁱ[ℝ] E) (S : Set E) {x : E}
      (hx : x ∈ S.extremePoints ℝ) : f x ∈ (f '' S).extremePoints ℝ := by
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro y ⟨a, ha, rfl⟩ z ⟨b, hb, rfl⟩ hseg
    have himage : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
      image_openSegment ℝ f.toAffineMap a b
    rw [← himage] at hseg
    have hab := hx.2 ha hb (f.injective.mem_set_image.mp hseg)
    exact ⟨congrArg f hab.1, congrArg f hab.2⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact forward g P hx
  · intro x hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    have hh := forward g.symm (g '' P) hx
    have himage : g.symm '' (g '' P) = P := by
      ext y
      simp
    rwa [himage] at hh

/-- The canonical finite set of actual vertices. -/
noncomputable def vertices (P : Set E) (hP : FinitePolytope P) : Finset E :=
  (finitePolytope_extremePoints_finite hP).toFinset

@[simp] theorem coe_vertices (P : Set E) (hP : FinitePolytope P) :
    (vertices P hP : Set E) = P.extremePoints ℝ := Set.Finite.coe_toFinset _

@[simp] theorem mem_vertices {P : Set E} (hP : FinitePolytope P) (v : E) :
    v ∈ vertices P hP ↔ v ∈ P.extremePoints ℝ := by
  rw [← Finset.mem_coe, coe_vertices]

theorem vertices_nonempty {P : Set E} (hP : FinitePolytope P) :
    (vertices P hP).Nonempty := by
  obtain ⟨v, hv⟩ := finitePolytope_extremePoints_nonempty hP
  exact ⟨v, (mem_vertices hP v).mpr hv⟩

theorem convexHull_vertices {P : Set E} (hP : FinitePolytope P) :
    convexHull ℝ (vertices P hP : Set E) = P := by
  rw [coe_vertices, ← finitePolytope_eq_convexHull_extremePoints hP]

/-- Hull symmetries supply precisely the finite-set transitivity required
by `CompositionSphere`. -/
theorem vertexTransitive_vertices {P : Set E} (hP : FinitePolytope P)
    (htrans : VertexTransitive P) : VertexTransitiveFinset (vertices P hP) := by
  intro v hv w hw
  obtain ⟨g, hg, hgv⟩ := htrans v ((mem_vertices hP v).mp hv)
    w ((mem_vertices hP w).mp hw)
  refine ⟨g, ?_, hgv⟩
  rw [coe_vertices, affineIsometry_image_extremePoints, hg]

/-- Set-level edges agree with the existing finite-set edge predicate on
the canonical actual vertices. -/
theorem edge_iff_vertices_isEdge {P : Set E} (hP : FinitePolytope P) (v w : E) :
    Edge P v w ↔ IsEdge (vertices P hP) v w := by
  simp only [Edge, IsEdge, mem_vertices, convexHull_vertices]

/-- A geometric transitive finite polytope has a sphere through all actual
vertices centered at their arithmetic centroid. -/
theorem finitePolytope_transitive_cospherical {P : Set E} (hP : FinitePolytope P)
    (htrans : VertexTransitive P) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ P.extremePoints ℝ,
      ‖v - vertexCentroid (vertices P hP)‖ ^ 2 = R ^ 2 := by
  obtain ⟨R, hR, hsphere⟩ := vertexTransitive_cospherical (vertices P hP)
    (vertices_nonempty hP) (vertexTransitive_vertices hP htrans)
  exact ⟨R, hR, fun v hv => hsphere v ((mem_vertices hP v).mpr hv)⟩

theorem finitePolytope_transitive_separated {P : Set E} (hP : FinitePolytope P)
    (htrans : VertexTransitive P) (hunit : UnitEdges P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) : 1 ≤ dist v w := by
  apply transitive_unit_edges_separated (vertices P hP) (vertexTransitive_vertices hP htrans)
    (fun x y hxy => hunit x y ((edge_iff_vertices_isEdge hP x y).mpr hxy))
  · exact (mem_vertices hP v).mpr hv
  · exact (mem_vertices hP w).mpr hw
  · exact hvw

theorem finitePolytope_transitive_edge_iff_dist_one {P : Set E} (hP : FinitePolytope P)
    (htrans : VertexTransitive P) (hunit : UnitEdges P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) :
    Edge P v w ↔ dist v w = 1 := by
  rw [edge_iff_vertices_isEdge hP]
  exact transitive_isEdge_iff_dist_eq_one (vertices P hP) (vertexTransitive_vertices hP htrans)
    (fun x y hxy => hunit x y ((edge_iff_vertices_isEdge hP x y).mpr hxy))
    ((mem_vertices hP v).mpr hv) ((mem_vertices hP w).mpr hw)

/-- Uniformity in dimensions at least three directly supplies vertex
transitivity. -/
theorem uniform_vertexTransitive {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    VertexTransitive P := by
  unfold Uniform at hP
  exact hP.2.2.1

/-- Sphere lemma for actual geometric uniform polytopes, with no additional
geometric assumption. -/
theorem uniform_cospherical {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    ∃ c : E, ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ P.extremePoints ℝ,
      ‖v - c‖ ^ 2 = R ^ 2 := by
  exact ⟨vertexCentroid (vertices P (uniform_finitePolytope hP)),
    finitePolytope_transitive_cospherical (uniform_finitePolytope hP)
      (uniform_vertexTransitive hP)⟩

/-- The arithmetic centroid of the actual vertices is intrinsically
interior to the polytope. The centroid premise of the earlier geometric
lemmas is thus proved from a finite polytope. -/
theorem vertexCentroid_mem_intrinsicInterior [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) :
    vertexCentroid (vertices P hP) ∈ intrinsicInterior ℝ P := by
  have hV := vertices_nonempty hP
  have hc : ((vertices P hP).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hV)
  have hsum : ∑ x ∈ vertices P hP, x =
      ((vertices P hP).card : ℝ) • vertexCentroid (vertices P hP) := by
    rw [vertexCentroid_eq_mean _ hV, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hint := finset_mean_mem_intrinsicInterior_convexHull (vertices P hP) hV
    (vertexCentroid (vertices P hP)) hsum
  simpa only [convexHull_vertices] using hint

/-- A sphere through all vertices of a positive-dimensional uniform
polytope cannot have zero radius. -/
theorem uniform_sphere_radius_pos {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P)
    {c : E} {R : ℝ} (hR : 0 ≤ R)
    (hsphere : ∀ v ∈ P.extremePoints ℝ, ‖v - c‖ ^ 2 = R ^ 2) : 0 < R := by
  by_contra hpos
  have hzero : R = 0 := le_antisymm (le_of_not_gt hpos) hR
  have hvertex : P.extremePoints ℝ ⊆ {c} := by
    intro v hv
    have hvzero : ‖v - c‖ ^ 2 = 0 := by simpa [hzero] using hsphere v hv
    have hvc : v = c := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hvzero))
    exact hvc
  have hsub : P ⊆ {c} := by
    rw [finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope hP)]
    exact convexHull_min hvertex (convex_singleton c)
  obtain ⟨x, hx⟩ := finitePolytope_nonempty (uniform_finitePolytope hP)
  have hxc : x = c := hsub hx
  have hc : c ∈ P := hxc ▸ hx
  have heq : P = {c} := hsub.antisymm (Set.singleton_subset_iff.mpr hc)
  have hd := uniform_dimension hP
  rw [heq, affineDimension_singleton] at hd
  omega

/-- The circumsphere of a genuine uniform polytope has positive radius. -/
theorem uniform_cospherical_pos {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    ∃ c : E, ∃ R : ℝ, 0 < R ∧ ∀ v ∈ P.extremePoints ℝ,
      ‖v - c‖ ^ 2 = R ^ 2 := by
  obtain ⟨c, R, hR, hsphere⟩ := uniform_cospherical hP
  exact ⟨c, R, uniform_sphere_radius_pos hP hR hsphere, hsphere⟩

/-- A uniform polytope of the ambient Euclidean dimension spans the
whole affine space; full span is not an extra classification hypothesis. -/
theorem uniform_affineSpan_eq_top {n : ℕ} {P : Set (Space (n + 3))}
    (hP : Uniform (n + 3) P) : affineSpan ℝ P = ⊤ := by
  have hd : (affineSpan ℝ P).direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [finrank_euclideanSpace_fin] using uniform_dimension hP
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp hd
  obtain ⟨x, hx⟩ := finitePolytope_nonempty (uniform_finitePolytope hP)
  exact ⟨x, subset_affineSpan ℝ P hx⟩

/-- The dimension-five specialization used in the main theorem. -/
theorem uniform5_affineSpan_eq_top {P : Set (Space 5)} (hP : Uniform 5 P) :
    affineSpan ℝ P = ⊤ := uniform_affineSpan_eq_top (n := 2) hP

/-- Paper separation lemma specialized to the actual recursive definition
of a unit-edge uniform polytope. -/
theorem unitUniform_separated {n : ℕ} {P : Set E} (hP : UnitUniform (n + 3) P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) : 1 ≤ dist v w :=
  finitePolytope_transitive_separated (uniform_finitePolytope hP.1)
    (uniform_vertexTransitive hP.1) hP.2 hv hw hvw

/-- In a genuine unit-edge uniform polytope, two actual vertices are
adjacent exactly when their distance is one. -/
theorem unitUniform_edge_iff_dist_one {n : ℕ} {P : Set E} (hP : UnitUniform (n + 3) P)
    {v w : E} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) :
    Edge P v w ↔ dist v w = 1 :=
  finitePolytope_transitive_edge_iff_dist_one (uniform_finitePolytope hP.1)
    (uniform_vertexTransitive hP.1) hP.2 hv hw

/-- Sanity check: a singleton is a genuine finite polytope. -/
theorem finitePolytope_singleton (v : E) : FinitePolytope ({v} : Set E) := by
  refine ⟨{v}, Finset.singleton_nonempty v, ?_⟩
  simp

/-- Sanity check: extracting actual vertices from a singleton returns
exactly the singleton. -/
@[simp] theorem vertices_singleton (v : E) :
    vertices ({v} : Set E) (finitePolytope_singleton v) = {v} := by
  apply Finset.coe_injective
  simp [extremePoints_singleton]

/-- Sanity check: a nondegenerate segment and its two endpoints give a
finite polytope; this does not require the endpoints to span the ambient space. -/
theorem finitePolytope_segment (v w : E) : FinitePolytope (segment ℝ v w) := by
  classical
  refine ⟨{v, w}, by simp, ?_⟩
  simp [convexHull_pair]

end Uniform5.Composition
