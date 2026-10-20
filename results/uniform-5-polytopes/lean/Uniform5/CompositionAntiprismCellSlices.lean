import Uniform5.CompositionAntiprismPrismSpecifiedCell
import Uniform5.CompositionProductSliceTransport

/-! Whole antiprism-cell transport through an actual antiprism-prism facet. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The literal endpoint slice is a three-dimensional facet of the actual
unit-uniform prism model. -/
theorem antiprismPrism_base_facet {n : ℕ} (hn : 3 ≤ n)
    (hM : UnitUniform 4 (antiprismPrismModel n)) {s : Space 1}
    (hs : s ∈ unitInterval.extremePoints ℝ) :
    Facet (antiprismPrismModel n) (product (antiprismModel n) {s}) := by
  have hA := antiprismPrism_base_uniform hn hM
  have hface := product_left_slice_face (finitePolytope_convex (uniform_finitePolytope hA.1)) hs
  rw [product_left_slice_image] at hface
  refine ⟨hface, product_nonempty (finitePolytope_nonempty (uniform_finitePolytope hA.1))
    (Set.singleton_nonempty s), ?_⟩
  rw [← product_left_slice_image, affineDimension_affineIsometry_image,
    uniform_dimension hA.1, uniform_dimension hM.1]

/-- Every vertex of a containing antiprism-prism facet lies in an actual
antiprism cell which is an orthogonal translate of the specified cell. -/
theorem unitUniform4_antiprismPrism_cell_translate {K G C : Set E} {n : ℕ}
    (hK : UnitUniform 4 K) (hn : 5 ≤ n) (hmodel : Congruent K (antiprismPrismModel n))
    (hG : PolygonFace K G n) (hC : Facet K C) (hGC : G ⊆ C)
    (hCA : Congruent C (antiprismModel n)) {w : E} (hw : w ∈ K.extremePoints ℝ) :
    ∃ d ∈ CaseB.normals C, Facet K (CaseB.translate C d) ∧
      Congruent (CaseB.translate C d) (antiprismModel n) ∧ w ∈ CaseB.translate C d := by
  have hn3 : 3 ≤ n := by omega
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 3 1).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 3 1).toAffineIsometry
  have hj : j '' antiprismPrismModel n = K := by
    change (f ∘ flattenProduct 3 1) '' antiprismPrismModel n = K
    rw [Set.image_comp]; exact hf
  have hM := (unitUniform_cross_congruent_iff hmodel 4).mp hK
  have hA := antiprismPrism_base_uniform hn3 hM
  have hG' : PolygonFace (j '' antiprismPrismModel n) G n := by rw [hj]; exact hG
  have hG₀ := embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hG'
  have hGim := embedding_face_image_preimage j hG'.1
  obtain ⟨A, s, hAs, hs, hslice⟩ := polyhedralPrism_nonquadrilateral_polygon_slice
    (uniform_finitePolytope hA.1) hG₀ (by omega)
  have hsliceFacet (t : Space 1) (ht : t ∈ unitInterval.extremePoints ℝ) :
      Facet K (j '' product (antiprismModel n) {t}) := by
    have hh := embedding_facet_image j (antiprismPrism_base_facet hn3 hM ht)
    rwa [hj] at hh
  have hsliceCong (t : Space 1) :
      Congruent (j '' product (antiprismModel n) {t}) (antiprismModel n) := by
    apply congruent_trans (congruent_symm (congruent_affineIsometry_image j _))
    rw [← product_left_slice_image]
    exact congruent_symm (congruent_affineIsometry_image (productLeftSlice t) _)
  have hGbase : G ⊆ j '' product (antiprismModel n) {s} := by
    rw [← hGim, hslice]
    apply Set.image_mono
    rintro z ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, hAs.1.2.1 ha, b, hb, rfl⟩
  have hbase := antiprismPrism_antiprism_cell_unique hK hn hmodel hG
    (hsliceFacet s hs) hC hGbase hGC (hsliceCong s) hCA
  rw [← hj, ← embedding_extremePoints, antiprismPrismModel, polyhedralPrismModel,
    product_extremePoints] at hw
  obtain ⟨_, ⟨x, hx, t, ht, rfl⟩, rfl⟩ := hw
  obtain ⟨d, hd, he⟩ := embedding_product_slice_transport j (antiprismModel n) s t
  rw [hbase] at hd he
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · rw [← he]; exact hsliceFacet t ht
  · rw [← he]; exact hsliceCong t
  · rw [← he]
    exact ⟨productPoint x t, ⟨x, hx.1, t, rfl, rfl⟩, rfl⟩

end Uniform5.Composition
