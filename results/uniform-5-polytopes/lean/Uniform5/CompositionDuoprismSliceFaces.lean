import Uniform5.CompositionActualDuoprismChart
import Uniform5.CompositionProductSliceTransport

/-! Every vertex of a duoprism belongs to an actual polygon face that is
an orthogonal translate of any fixed nonquadrilateral polygon face. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem embedded_duoprism_slice_at_vertex {p q : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (f : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2) →ᵃⁱ[ℝ] E)
    (y : Plane) {w : E} (hw : w ∈ (f '' duoprismModel p q).extremePoints ℝ) :
    ∃ d ∈ CaseB.normals (f '' product (unitPolygon p) {y}),
      PolygonFace (f '' duoprismModel p q)
        (CaseB.translate (f '' product (unitPolygon p) {y}) d) p ∧
      w ∈ CaseB.translate (f '' product (unitPolygon p) {y}) d := by
  rw [← embedding_extremePoints, duoprismModel, product_extremePoints] at hw
  obtain ⟨_, ⟨x, hx, z, hz, rfl⟩, rfl⟩ := hw
  obtain ⟨d, hd, he⟩ := embedding_product_slice_transport f (unitPolygon p) y z
  refine ⟨d, hd, ?_, ?_⟩
  · rw [← he]
    apply embedding_polygonFace_image f
    simpa only [product_left_slice_image] using
      product_left_polygonFace (convex_convexHull ℝ _) (unitPolygon_self_polygonFace hp) hz
  · rw [← he]
    exact ⟨productPoint x z, ⟨x, hx.1, z, rfl, rfl⟩, rfl⟩

/-- The complete whole-face transport statement needs no edge assumption
on w. Both possible polygon factors are handled in a single embedding. -/
theorem unitUniform4_duoprism_polygon_translate {K G : Set E} {p q n : ℕ}
    (hK : UnitUniform 4 K) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel p q)) (hG : PolygonFace K G n)
    (hn : n ≠ 4) {w : E} (hw : w ∈ K.extremePoints ℝ) :
    ∃ d ∈ CaseB.normals G, PolygonFace K (CaseB.translate G d) n ∧
      w ∈ CaseB.translate G d := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 2 2).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 2 2).toAffineIsometry
  have hj : j '' duoprismModel p q = K := by
    change (f ∘ flattenProduct 2 2) '' duoprismModel p q = K
    rw [Set.image_comp]
    exact hf
  have hM := (unitUniform_cross_congruent_iff hmodel 4).mp hK
  have hG' : PolygonFace (j '' duoprismModel p q) G n := hj ▸ hG
  let G₀ := j ⁻¹' G
  have hG₀ : PolygonFace (duoprismModel p q) G₀ n :=
    embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hG'
  have hGim : j '' G₀ = G := embedding_face_image_preimage j hG'.1
  rcases duoprism_nonquadrilateral_polygon_slices hp hq hG₀ hn with
    ⟨hnp, y, hy, hs⟩ | ⟨hnq, x, hx, hs⟩
  · have hh := embedded_duoprism_slice_at_vertex hp hq j y (hj.symm ▸ hw)
    rwa [← hs, hGim, hj, ← hnp] at hh
  · let f' := j.comp planarProductSwap.toAffineIsometry
    have hf' : f' '' duoprismModel q p = K := by
      change (j ∘ planarProductSwap) '' product (unitPolygon q) (unitPolygon p) = K
      rw [Set.image_comp, planarProductSwap_image]
      exact hj
    have hg' : f' '' product (unitPolygon q) {x} = G := by
      change (j ∘ planarProductSwap) '' product (unitPolygon q) {x} = G
      rw [Set.image_comp, planarProductSwap_image, ← hs]
      exact hGim
    have hh := embedded_duoprism_slice_at_vertex hq hp f' x (hf'.symm ▸ hw)
    rwa [hg', hf', ← hnq] at hh

end Uniform5.Composition
