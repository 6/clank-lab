import Uniform5.CompositionSingleFanCover

/-! The B2 large-facet argument gives an actual two-fan cover whenever
all large polygons through the root are the specified pair. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Coverage by two actual polygons, without assuming either polygon's
cycle, metric chart, or fan covers the vertex figure. -/
def TwoLargeFacesCoverAt (P : Set (Space 5)) (v : Space 5)
    (G H : Set (Space 5)) : Prop :=
  ∀ F k, PolygonFace P F k → 17 ≤ k → v ∈ F.extremePoints ℝ → F = G ∨ F = H

theorem TwoLargeFacesCoverAt.image {P G H : Set (Space 5)} {v : Space 5}
    (h : TwoLargeFacesCoverAt P v G H) (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) :
    TwoLargeFacesCoverAt (g '' P) (g v) (g '' G) (g '' H) := by
  intro F k hF hk hvF
  have hback : PolygonFace P (g.symm '' F) k := by
    simpa only [affineIsometry_symm_image_image] using polygonFace_image g.symm hF
  have hvback : v ∈ (g.symm '' F).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints]
    exact ⟨g v, hvF, g.symm_apply_apply v⟩
  rcases h _ k hback hk hvback with he | he
  · left
    calc
      F = g '' (g.symm '' F) := (affineIsometry_image_symm_image g F).symm
      _ = g '' G := congrArg (fun A => g '' A) he
  · right
    calc
      F = g '' (g.symm '' F) := (affineIsometry_image_symm_image g F).symm
      _ = g '' H := congrArg (fun A => g '' A) he

theorem unitUniform5_two_fan_edge_cover
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : 17 ≤ k)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (∃ i : Fin D.length, Facet V (D.facet i ∩ V) ∧ segment ℝ x y ⊆ D.facet i ∩ V) ∨
    (∃ j : Fin A.length, Facet V (A.facet j ∩ V) ∧ segment ℝ x y ⊆ A.facet j ∩ V) := by
  obtain ⟨K, hK, _, hKV, heK, F, n, hF, hn, hvF, hFK⟩ :=
    unitUniform5_figure_edge_in_large_fan classification3D classification4D N S
      hLIB hS1 hB2 hP ⟨G, k, hG, hk⟩ hv he
  rcases hcover F n hF hn hvF with hFG | hFH
  · subst F
    obtain ⟨i, hi⟩ := (D.facet_coverage K).mp ⟨hK, hFK⟩
    exact Or.inl ⟨i, hi.symm ▸ hKV, hi.symm ▸ heK⟩
  · subst F
    obtain ⟨i, hi⟩ := (A.facet_coverage K).mp ⟨hK, hFK⟩
    exact Or.inr ⟨i, hi.symm ▸ hKV, hi.symm ▸ heK⟩

theorem unitUniform5_two_fan_vertex_cover
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : 17 ≤ k)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    {x : Space 5}
    (hx : x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (∃ i : Fin D.length, x ∈ (D.facet i ∩ V).extremePoints ℝ) ∨
    (∃ j : Fin A.length, x ∈ (A.facet j ∩ V).extremePoints ℝ) := by
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  obtain ⟨f, Q, him, _, _, hQ, hdQ, _⟩ := unitUniform5_vertexFigure_centered_model hP hv
  have hV : FinitePolytope V := by
    rw [show V = f '' Q from him.symm]
    exact finitePolytope_affineMap_image f.toAffineMap hQ
  have hdV : affineDimension V = 4 := by
    rw [show V = f '' Q from him.symm, affineDimension_affineIsometry_image, hdQ]
  have hdeg := finitePolytope_neighbour_card_lower hV hx (by rw [hdV]; norm_num)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (geometricNeighbours V hV x).card by omega)
  have he := (mem_geometricNeighbours V hV x y).mp hy
  rcases unitUniform5_two_fan_edge_cover classification3D classification4D N S
    hLIB hS1 hB2 hP hG hk hv hcover D A he with ⟨i, hi, hc⟩ | ⟨j, hj, hc⟩
  · left
    refine ⟨i, ?_⟩
    rw [face_extremePoints_eq hi.1]
    exact ⟨hc (left_mem_segment ℝ x y), hx⟩
  · right
    refine ⟨j, ?_⟩
    rw [face_extremePoints_eq hj.1]
    exact ⟨hc (left_mem_segment ℝ x y), hx⟩

end Uniform5.Composition
