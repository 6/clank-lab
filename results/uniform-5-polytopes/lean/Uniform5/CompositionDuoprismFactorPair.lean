import Uniform5.CompositionActualDuoprismChart
import Uniform5.CompositionProductEdges

/-! Both complementary polygon factors occur through every actual vertex
of a duoprism, even when their parameters coincide. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitUniform4_duoprism_factor_pair_at_vertex {K : Set E} {n m : ℕ}
    (hK : UnitUniform 4 K) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hmodel : Congruent K (duoprismModel n m))
    {v : E} (hv : v ∈ K.extremePoints ℝ) :
    ∃ G H, PolygonFace K G n ∧ PolygonFace K H m ∧
      v ∈ G.extremePoints ℝ ∧ v ∈ H.extremePoints ℝ ∧ G ≠ H := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 2 2).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 2 2).toAffineIsometry
  have hj : j '' duoprismModel n m = K := by
    change (f ∘ flattenProduct 2 2) '' duoprismModel n m = K
    rw [Set.image_comp]
    exact hf
  rw [← hj, ← embedding_extremePoints, duoprismModel, product_extremePoints] at hv
  obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩ := hv
  let G := productLeftSlice y '' unitPolygon n
  let H := productRightSlice x '' unitPolygon m
  have hG : PolygonFace (duoprismModel n m) G n :=
    product_left_polygonFace (convex_convexHull ℝ _) (unitPolygon_self_polygonFace hn) hy
  have hH : PolygonFace (duoprismModel n m) H m := by
    have hh := embedding_polygonFace_image (productRightSlice x) (unitPolygon_self_polygonFace hm)
    exact ⟨product_right_slice_face (convex_convexHull ℝ _) hx, hh.2⟩
  have hvG : productPoint x y ∈ G.extremePoints ℝ := by
    rw [← embedding_extremePoints]
    exact ⟨x, hx, rfl⟩
  have hvH : productPoint x y ∈ H.extremePoints ℝ := by
    rw [← embedding_extremePoints]
    exact ⟨y, hy, rfl⟩
  have hne : G ≠ H := by
    intro he
    obtain ⟨a, b, _, ha, _⟩ := unitPolygon_neighbor_pair hn hx
    have ham : productPoint a y ∈ G := ⟨a, ha.2.1.1, rfl⟩
    rw [he, show H = product {x} (unitPolygon m) from product_right_slice_image _ _] at ham
    have hax := (productPoint_mem_product.mp ham).1
    exact ha.2.2.1 hax.symm
  refine ⟨j '' G, j '' H, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hj]; exact embedding_polygonFace_image j hG
  · rw [← hj]; exact embedding_polygonFace_image j hH
  · rw [← embedding_extremePoints]; exact ⟨_, hvG, rfl⟩
  · rw [← embedding_extremePoints]; exact ⟨_, hvH, rfl⟩
  · exact fun he => hne ((Set.image_injective.mpr j.injective) he)

/-- The two factor polygons are actual parent faces, not merely sections
inside an abstract model. -/
theorem unitUniform5_duoprism_factor_pair_at_vertex
    {P K : Set (Space 5)} (hP : UnitUniform 5 P) (hK : Facet P K)
    {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hmodel : Congruent K (duoprismModel n m))
    {v : Space 5} (hv : v ∈ K.extremePoints ℝ) :
    ∃ G H, PolygonFace P G n ∧ PolygonFace P H m ∧ G ⊆ K ∧ H ⊆ K ∧
      v ∈ G.extremePoints ℝ ∧ v ∈ H.extremePoints ℝ ∧ G ≠ H := by
  obtain ⟨G, H, hG, hH, hvG, hvH, hne⟩ :=
    unitUniform4_duoprism_factor_pair_at_vertex (unitUniform_facet hP hK) hn hm hmodel hv
  exact ⟨G, H, ⟨face_of_face hK.1 hG.1, hG.2⟩, ⟨face_of_face hK.1 hH.1, hH.2⟩,
    hG.1.2.1, hH.1.2.1, hvG, hvH, hne⟩

end Uniform5.Composition
