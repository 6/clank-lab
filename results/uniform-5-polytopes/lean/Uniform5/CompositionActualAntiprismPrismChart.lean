import Uniform5.CompositionAntiprismPrismChartTransport
import Uniform5.CompositionFigurePlacement

/-! The F3 pyramid for an actual antiprism-prism facet and selected polygon. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual model uniformity descends to its antiprism factor. -/
theorem antiprismPrism_base_uniform {n : ℕ} (hn : 3 ≤ n)
    (hM : UnitUniform 4 (antiprismPrismModel n)) : UnitUniform 3 (antiprismModel n) := by
  have hfin := antiprismModel_finitePolytope (by omega : 0 < n)
  have hne := finitePolytope_nonempty hfin
  have hd : affineDimension (antiprismModel n) = 3 := by
    have hh := uniform_dimension hM.1
    change affineDimension (product (antiprismModel n) unitInterval) = 4 at hh
    rw [affineDimension_product hne (finitePolytope_nonempty unitInterval_finitePolytope),
      unitInterval_affineDimension] at hh
    omega
  obtain ⟨s, hs⟩ := finitePolytope_extremePoints_nonempty unitInterval_finitePolytope
  have hface := product_left_slice_face (finitePolytope_convex hfin) hs
  have hd' : affineDimension (productLeftSlice s '' antiprismModel n) = 3 := by
    rw [affineDimension_affineIsometry_image]; exact hd
  have hu := unitUniform_face hM hface (hne.image _) (by omega : 2 ≤ affineDimension
    (productLeftSlice s '' antiprismModel n))
  rw [hd'] at hu
  exact (unitUniform_cross_congruent_iff
    (congruent_affineIsometry_image (productLeftSlice s) (antiprismModel n)) 3).mpr hu

/-- Every actual large polygon in an antiprism prism selects its antiprism
cell and the exact complete five-neighbor pyramid chart. -/
theorem unitUniform4_antiprismPrism_neighbor_chart {K G : Set E} {v : E} {n k : ℕ}
    (hK : UnitUniform 4 K) (hn : 3 ≤ n) (hk : 5 ≤ k)
    (hmodel : Congruent K (antiprismPrismModel n)) (hG : PolygonFace K G k)
    (hv : v ∈ G.extremePoints ℝ) :
    k = n ∧ ∃ C, Facet K C ∧ G ⊆ C ∧ Congruent C (antiprismModel n) ∧
      Nonempty (AntiprismPrismNeighborChart K C G v n) := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 3 1).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 3 1).toAffineIsometry
  have hj : j '' antiprismPrismModel n = K := by
    change (f ∘ flattenProduct 3 1) '' antiprismPrismModel n = K
    rw [Set.image_comp]; exact hf
  have hM := (unitUniform_cross_congruent_iff hmodel 4).mp hK
  have hA := antiprismPrism_base_uniform hn hM
  have hG' : PolygonFace (j '' antiprismPrismModel n) G k := by rw [hj]; exact hG
  have hG₀ := embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hG'
  have hGim := embedding_face_image_preimage j hG'.1
  have hvK := hG.1.2.extremePoints_subset_extremePoints hv
  rw [← hj, ← embedding_extremePoints] at hvK
  obtain ⟨v₀, hv₀, rfl⟩ := hvK
  have hvm : v₀ ∈ j ⁻¹' G := hv.1
  rw [antiprismPrismModel, polyhedralPrismModel, product_extremePoints] at hv₀
  obtain ⟨x, hx, y, hy, he⟩ := hv₀
  subst v₀
  obtain ⟨A, s, hAs, hs, hslice⟩ := polyhedralPrism_nonquadrilateral_polygon_slice
    (uniform_finitePolytope hA.1) hG₀ (by omega)
  have hys : y = s := by rw [hslice, productPoint_mem_product] at hvm; exact hvm.2
  subst s
  have hxA : x ∈ A.extremePoints ℝ := by
    rw [face_extremePoints_eq hAs.1]
    refine ⟨?_, hx⟩
    rw [hslice, productPoint_mem_product] at hvm
    exact hvm.1
  obtain ⟨hkn, D⟩ := antiprism_neighbor_chart hn hk hA hAs hxA
  obtain ⟨D⟩ := D
  obtain ⟨T⟩ := antiprismPrism_product_chart D hA (uniform_finitePolytope hM.1) hx hy
  have hCF := product_left_slice_face (finitePolytope_convex (uniform_finitePolytope hA.1)) hy
  rw [product_left_slice_image] at hCF
  have hdC : affineDimension (product (antiprismModel n) {y}) = 3 := by
    rw [← product_left_slice_image, affineDimension_affineIsometry_image]
    exact uniform_dimension hA.1
  have hCfacet : Facet (antiprismPrismModel n) (product (antiprismModel n) {y}) :=
    ⟨hCF, product_nonempty (finitePolytope_nonempty (uniform_finitePolytope hA.1))
      (Set.singleton_nonempty y), by rw [hdC, uniform_dimension hM.1]⟩
  have hCj := embedding_facet_image j hCfacet
  rw [hj] at hCj
  refine ⟨hkn, j '' product (antiprismModel n) {y}, hCj, ?_, ?_, ?_⟩
  · rw [← hGim, hslice]
    apply Set.image_mono
    rintro z ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, hAs.1.2.1 ha, b, hb, rfl⟩
  · apply congruent_trans (congruent_symm (congruent_affineIsometry_image j _))
    rw [← product_left_slice_image]
    exact congruent_symm (congruent_affineIsometry_image (productLeftSlice y) _)
  · have ht := T.map j
    change AntiprismPrismNeighborChart (j '' antiprismPrismModel n) _ _ _ n at ht
    rw [hj, ← hslice, hGim] at ht
    exact ⟨ht⟩

end Uniform5.Composition
