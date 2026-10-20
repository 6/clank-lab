import Uniform5.Separation
import Uniform5.Centroid
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-! The sphere input from finite vertex transitivity. -/
noncomputable section
namespace Uniform5
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetry of a nonempty finite vertex set fixes its actual centroid. -/
theorem finite_symmetry_fixes_centroid (V : Finset E) (hne : V.Nonempty)
    (T : E ≃ᵃⁱ[ℝ] E) (hT : T '' (V : Set E) = (V : Set E)) :
    T (V.centroid ℝ id) = V.centroid ℝ id := by
  have h := V.map_affineCombination id (V.centroidWeights ℝ)
    (V.sum_centroidWeights_eq_one_of_nonempty ℝ hne) T.toAffineEquiv.toAffineMap
  change T (V.centroid ℝ id) = V.centroid ℝ T at h
  rw [h]
  apply V.centroid_eq_of_inj_on_of_image_eq ℝ V
    (fun i _ j _ hij => T.injective hij) (fun i _ j _ hij => hij)
  simpa using hT

/-- Vertex transitivity by actual ambient isometries gives a common radius
about the centroid; no sphere is assumed. -/
theorem vertex_transitive_cospherical (V : Finset E) (hne : V.Nonempty)
    (htrans : ∀ x ∈ V, ∀ y ∈ V, ∃ T : E ≃ᵃⁱ[ℝ] E,
      T '' (V : Set E) = (V : Set E) ∧ T x = y) :
    ∃ R : ℝ, ∀ x ∈ V, dist x (V.centroid ℝ id) = R := by
  obtain ⟨r, hr⟩ := hne
  refine ⟨dist r (V.centroid ℝ id), ?_⟩
  intro x hx
  obtain ⟨T, hT, hTx⟩ := htrans r hr x hx
  calc
    dist x (V.centroid ℝ id) = dist (T r) (T (V.centroid ℝ id)) := by
      rw [hTx, finite_symmetry_fixes_centroid V ⟨r, hr⟩ T hT]
    _ = dist r (V.centroid ℝ id) := T.dist_map r (V.centroid ℝ id)

/-- Consequently the exposed-edge graph of a vertex-transitive finite set
is connected without a separate sphere or graph-connectivity premise. -/
theorem vertex_transitive_edge_graph_connected (V : Finset E)
    (htrans : ∀ x ∈ V, ∀ y ∈ V, ∃ T : E ≃ᵃⁱ[ℝ] E,
      T '' (V : Set E) = (V : Set E) ∧ T x = y)
    {r s : E} (hr : r ∈ V) (hs : s ∈ V) :
    Relation.ReflTransGen (IsEdge V) r s := by
  obtain ⟨R, hR⟩ := vertex_transitive_cospherical V ⟨r, hr⟩ htrans
  apply cospherical_edge_graph_connected V (c := V.centroid ℝ id) (R := R) _ hr hs
  intro x hx
  rw [← dist_eq_norm, hR x hx]

end Uniform5
