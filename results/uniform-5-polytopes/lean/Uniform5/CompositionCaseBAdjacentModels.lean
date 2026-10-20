import Uniform5.CompositionCaseBCellModels
import Uniform5.CompositionProductModelIncidence

/-! The actual two-cell incidence required by Fact F3, transported into
arbitrary ambient Euclidean spaces. Model uniformity is derived from the
actual facet, rather than supplied as an additional premise. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- Distinct cells at a nonquadrilateral polygon in an antiprism-prism
are one antiprism and one polygon prism, in one of the two orders. -/
theorem antiprismPrism_distinct_cell_models {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hM : UnitUniform 4 (antiprismPrismModel n))
    {G C D : Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1))}
    (hG : PolygonFace (antiprismPrismModel n) G n)
    (hC : IsConvexFace (antiprismPrismModel n) C)
    (hD : IsConvexFace (antiprismPrismModel n) D)
    (hdC : affineDimension C = 3) (hdD : affineDimension D = 3)
    (hGC : G ⊆ C) (hGD : G ⊆ D) (hCD : C ≠ D) :
    (Congruent C (antiprismModel n) ∧ Congruent D (polygonPrismModel n)) ∨
    (Congruent C (polygonPrismModel n) ∧ Congruent D (antiprismModel n)) := by
  have hAnti := antiprismModel_finitePolytope (by omega : 0 < n)
  obtain ⟨A, y, hA, hy, he⟩ := polyhedralPrism_nonquadrilateral_polygon_slice hAnti hG hn4
  have hdAnti : affineDimension (antiprismModel n) = 3 := by
    have hd := uniform_dimension hM.1
    change affineDimension (product (antiprismModel n) unitInterval) = 4 at hd
    rw [affineDimension_product (finitePolytope_nonempty hAnti)
      (finitePolytope_nonempty unitInterval_finitePolytope), unitInterval_affineDimension] at hd
    omega
  have hcaseC := polyhedralPrism_cells_at_polygon_slice hdAnti hA hC
    ((polygonFace_nonempty hG).mono hGC) hdC (he ▸ hGC)
  have hcaseD := polyhedralPrism_cells_at_polygon_slice hdAnti hA hD
    ((polygonFace_nonempty hG).mono hGD) hdD (he ▸ hGD)
  have hbase : Congruent (product (antiprismModel n) {y}) (antiprismModel n) := by
    rw [product_singleton_right_image]
    exact congruent_symm (congruent_affineIsometry_image (productLeftSlice y) _)
  have hGA : Congruent G A := by
    rw [he, product_singleton_right_image]
    exact congruent_symm (congruent_affineIsometry_image (productLeftSlice y) A)
  obtain ⟨_, f, hf⟩ := polygonFace_unitPolygon hM hG
  have hg : Congruent G (unitPolygon n) := by
    rw [hf]
    exact congruent_symm (congruent_affineIsometry_image f _)
  have hside : Congruent (product A unitInterval) (polygonPrismModel n) :=
    congruent_product (congruent_trans (congruent_symm hGA) hg) (congruent_refl unitInterval)
  rcases hcaseC with hC' | hC' <;> rcases hcaseD with hD' | hD'
  · exact (hCD (hC'.trans hD'.symm)).elim
  · exact Or.inl ⟨hC'.symm ▸ hbase, hD'.symm ▸ hside⟩
  · exact Or.inr ⟨hC'.symm ▸ hside, hD'.symm ▸ hbase⟩
  · exact (hCD (hC'.trans hD'.symm)).elim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual adjacent cells of a duoprism facet are both n-prisms. -/
theorem unitUniform4_duoprism_word_cells {n q : ℕ}
    (hn : 3 ≤ n) (hq : 3 ≤ q) (hn4 : n ≠ 4)
    {K G A B : Set E} (hK : UnitUniform 4 K) (hG : PolygonFace K G n)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    (hKM : Congruent K (duoprismModel n q)) :
    Congruent A (polygonPrismModel n) ∧ Congruent B (polygonPrismModel n) := by
  obtain ⟨G', A', B', hG', hA', hB', hGA', hGB', hAB', _, hAA', hBB'⟩ :=
    actual_word_in_congruent_product_model (by decide : 2 + 2 = 4)
      hK hG hA hB hGA hGB hAB hKM
  have hM := (unitUniform_cross_congruent_iff hKM 4).mp hK
  have hdM := uniform_dimension hM.1
  have hdA : affineDimension A' = 3 := by have hh := hA'.2.2; omega
  have hdB : affineDimension B' = 3 := by have hh := hB'.2.2; omega
  exact ⟨congruent_trans hAA' (duoprism_cell_at_nonquadrilateral_polygon hn hq hn4
      hG' hA'.1 hdA hGA'),
    congruent_trans hBB' (duoprism_cell_at_nonquadrilateral_polygon hn hq hn4
      hG' hB'.1 hdB hGB')⟩

/-- The actual adjacent cells of an antiprism-prism facet are one of each
model. All geometry and uniformity come from the given actual facet. -/
theorem unitUniform4_antiprismPrism_word_cells {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4)
    {K G A B : Set E} (hK : UnitUniform 4 K) (hG : PolygonFace K G n)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    (hKM : Congruent K (antiprismPrismModel n)) :
    (Congruent A (antiprismModel n) ∧ Congruent B (polygonPrismModel n)) ∨
    (Congruent A (polygonPrismModel n) ∧ Congruent B (antiprismModel n)) := by
  obtain ⟨G', A', B', hG', hA', hB', hGA', hGB', hAB', _, hAA', hBB'⟩ :=
    actual_word_in_congruent_product_model (by decide : 3 + 1 = 4)
      hK hG hA hB hGA hGB hAB hKM
  have hM := (unitUniform_cross_congruent_iff hKM 4).mp hK
  have hdM := uniform_dimension hM.1
  have hdA : affineDimension A' = 3 := by have hh := hA'.2.2; omega
  have hdB : affineDimension B' = 3 := by have hh := hB'.2.2; omega
  rcases antiprismPrism_distinct_cell_models hn hn4 hM hG' hA'.1 hB'.1
    hdA hdB hGA' hGB' hAB' with ⟨hCA, hDB⟩ | ⟨hCA, hDB⟩
  · exact Or.inl ⟨congruent_trans hAA' hCA, congruent_trans hBB' hDB⟩
  · exact Or.inr ⟨congruent_trans hAA' hCA, congruent_trans hBB' hDB⟩

end Uniform5.Composition
