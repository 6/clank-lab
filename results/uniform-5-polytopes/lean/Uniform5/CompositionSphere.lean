import Uniform5.Sphere
import Uniform5.Propagation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# The sphere forced by a transitive finite vertex set

These definitions use actual ambient Euclidean isometries and the actual finite
vertex set. In particular, cosphericity is a conclusion, not a field of a
``uniform polytope`` structure or a classification hypothesis.
-/

open Set
open scoped BigOperators

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every two vertices are related by an ambient affine isometry preserving the
whole vertex set. Nonemptiness is stated separately when needed. -/
noncomputable abbrev VertexTransitiveFinset (V : Finset E) : Prop :=
  IsVertexTransitive (V : Set E)

/-- The arithmetic centroid, using Mathlib's affine centroid. -/
noncomputable def vertexCentroid (V : Finset E) : E := V.centroid ℝ id

/-- Every affine symmetry of a nonempty finite vertex set fixes its centroid. -/
theorem vertexCentroid_fixed (V : Finset E) (hV : V.Nonempty)
    (g : E ≃ᵃⁱ[ℝ] E) (hg : g '' (V : Set E) = (V : Set E)) :
    g (vertexCentroid V) = vertexCentroid V := by
  exact finite_symmetry_fixes_centroid V hV g hg

/-- The centroid is the usual sum divided by the number of vertices. -/
theorem vertexCentroid_eq_mean (V : Finset E) (hV : V.Nonempty) :
    vertexCentroid V = (V.card : ℝ)⁻¹ • ∑ x ∈ V, x := by
  unfold vertexCentroid
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (V.sum_centroidWeights_eq_one_of_nonempty ℝ hV)]
  simp only [Finset.centroidWeights_apply, id_eq, Finset.smul_sum]

/-- Translating vertices by their centroid gives zero sum. -/
theorem sum_sub_vertexCentroid (V : Finset E) (hV : V.Nonempty) :
    ∑ x ∈ V, (x - vertexCentroid V) = 0 := by
  have hc : (V.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hV)
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    vertexCentroid_eq_mean V hV, smul_smul, mul_inv_cancel₀ hc, one_smul, sub_self]

/-- Transitivity forces all vertices to have the same distance from their
centroid. -/
theorem transitive_dist_vertexCentroid (V : Finset E) (htrans : VertexTransitiveFinset V)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    dist v (vertexCentroid V) = dist w (vertexCentroid V) := by
  obtain ⟨g, hg, hgv⟩ := htrans v hv w hw
  have hgc := vertexCentroid_fixed V ⟨v, hv⟩ g hg
  simpa [hgv, hgc] using (g.dist_map v (vertexCentroid V)).symm

/-- A nonempty transitive finite vertex set lies on a sphere centered at its
centroid, with a nonnegative radius. -/
theorem vertexTransitive_cospherical (V : Finset E) (hV : V.Nonempty)
    (htrans : VertexTransitiveFinset V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ V, ‖x - vertexCentroid V‖ ^ 2 = R ^ 2 := by
  obtain ⟨R, hR⟩ := vertex_transitive_cospherical V hV htrans
  obtain ⟨v, hv⟩ := hV
  refine ⟨R, (hR v hv) ▸ dist_nonneg, ?_⟩
  intro x hx
  rw [← dist_eq_norm]
  exact congrArg (fun t : ℝ => t ^ 2) (hR x hx)

/-- The paper's separation conclusion now follows from vertex transitivity
and unit exposed edges alone. -/
theorem transitive_unit_edges_separated (V : Finset E)
    (htrans : VertexTransitiveFinset V)
    (hunit : ∀ v w, IsEdge V v w → dist v w = 1)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) :
    1 ≤ dist v w := by
  obtain ⟨R, _, hR⟩ := vertexTransitive_cospherical V ⟨v, hv⟩ htrans
  exact unit_edges_separated V hR hunit hv hw hvw

/-- Likewise, distance one is equivalent to adjacency, without assuming a
sphere as an extra geometric hypothesis. -/
theorem transitive_isEdge_iff_dist_eq_one (V : Finset E)
    (htrans : VertexTransitiveFinset V)
    (hunit : ∀ v w, IsEdge V v w → dist v w = 1)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    IsEdge V v w ↔ dist v w = 1 := by
  obtain ⟨R, _, hR⟩ := vertexTransitive_cospherical V ⟨v, hv⟩ htrans
  exact isEdge_iff_dist_eq_one V hR hunit hv hw

/-- Sanity check: a singleton is vertex transitive. -/
theorem vertexTransitive_singleton (v : E) : VertexTransitiveFinset {v} := by
  intro x hx y hy
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact ⟨AffineIsometryEquiv.refl ℝ E, by simp, rfl⟩

/-- Sanity check: the singleton centroid is its vertex. -/
@[simp] theorem vertexCentroid_singleton (v : E) : vertexCentroid {v} = v := by
  exact Finset.centroid_singleton ℝ id v

/-- Sanity check: every two-point configuration is vertex transitive; the
nontrivial symmetry is reflection through the midpoint. -/
theorem vertexTransitive_pair [DecidableEq E] (v w : E) : VertexTransitiveFinset {v, w} := by
  classical
  let g := AffineIsometryEquiv.pointReflection ℝ (midpoint ℝ v w)
  have hgv : g v = w := AffineIsometryEquiv.pointReflection_midpoint_left v w
  have hgw : g w = v := AffineIsometryEquiv.pointReflection_midpoint_right v w
  have hg : g '' ({v, w} : Finset E) = (({v, w} : Finset E) : Set E) := by
    simp only [Finset.coe_pair, Set.image_pair, hgv, hgw]
    exact Set.pair_comm w v
  intro x hx y hy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨AffineIsometryEquiv.refl ℝ E, by simp, rfl⟩
  · exact ⟨g, hg, hgv⟩
  · exact ⟨g, hg, hgw⟩
  · exact ⟨AffineIsometryEquiv.refl ℝ E, by simp, rfl⟩

end Uniform5
