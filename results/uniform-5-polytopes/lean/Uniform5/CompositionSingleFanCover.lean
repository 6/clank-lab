import Uniform5.CompositionLargeFacetCover
import Uniform5.CompositionFacetSystemGeneral
import Uniform5.CompositionFigureNormalization

/-! In the single-large-face case the actual polygon cycle supplies a
covering fan for all edges and vertices of the actual vertex figure. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Uniqueness as actual subsets, retaining the genuine polygon size and
apex incidence. This is the geometric meaning of the paper's case s = 1. -/
def UniqueLargeFaceAt (P : Set (Space 5)) (v : Space 5) (G : Set (Space 5)) : Prop :=
  ∀ F k, PolygonFace P F k → 17 ≤ k → v ∈ F.extremePoints ℝ → F = G

theorem unitUniform5_single_fan_edge_cover
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : 17 ≤ k)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hunique : UniqueLargeFaceAt P v G) (D : ActualPolygonCycle P G)
    {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ i : Fin D.length, Facet V (D.facet i ∩ V) ∧ segment ℝ x y ⊆ D.facet i ∩ V := by
  obtain ⟨K, hK, _, hKV, heK, F, n, hF, hn, hvF, hFK⟩ :=
    unitUniform5_figure_edge_in_large_fan classification3D classification4D N S
      hLIB hS1 hB2 hP ⟨G, k, hG, hk⟩ hv he
  have hFG := hunique F n hF hn hvF
  subst F
  obtain ⟨i, hi⟩ := (D.facet_coverage K).mp ⟨hK, hFK⟩
  exact ⟨i, hi.symm ▸ hKV, hi.symm ▸ heK⟩

/-- Edge coverage also covers every actual vertex; positivity of the
figure dimension supplies a genuine incident edge, without an extra fan
coverage premise. -/
theorem unitUniform5_single_fan_vertex_cover
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : 17 ≤ k)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hunique : UniqueLargeFaceAt P v G) (D : ActualPolygonCycle P G)
    {x : Space 5}
    (hx : x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ i : Fin D.length, x ∈ (D.facet i ∩ V).extremePoints ℝ := by
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  obtain ⟨f, Q, him, _, _, hQ, hdQ, _⟩ := unitUniform5_vertexFigure_centered_model hP hv
  have hV : FinitePolytope V := by
    rw [show V = f '' Q from him.symm]
    exact finitePolytope_affineMap_image f.toAffineMap hQ
  have hdV : affineDimension V = 4 := by
    rw [show V = f '' Q from him.symm, affineDimension_affineIsometry_image, hdQ]
  have hdeg := finitePolytope_neighbour_card_lower hV hx (by rw [hdV]; norm_num)
  have hne : (geometricNeighbours V hV x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hne
  have he := (mem_geometricNeighbours V hV x y).mp hy
  obtain ⟨i, hi, hcover⟩ := unitUniform5_single_fan_edge_cover
    classification3D classification4D N S hLIB hS1 hB2 hP hG hk hv hunique D he
  refine ⟨i, ?_⟩
  rw [face_extremePoints_eq hi.1]
  exact ⟨hcover (left_mem_segment ℝ x y), hx⟩

end Uniform5.Composition
