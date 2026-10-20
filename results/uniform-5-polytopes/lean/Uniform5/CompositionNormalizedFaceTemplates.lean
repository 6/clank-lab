import Uniform5.CompositionNormalizedLabels
import Uniform5.CompositionTemplateEmbedding
import Uniform5.CompositionFigureFacetCorrespondence

/-! Actual facet and ridge templates in normalized figure coordinates.
The parent face is recovered from the section, so the maps agree with
the globally coherent labels used by every edge cycle. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem actual_normalized_facet_template
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q F : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hF : Facet Q F) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    LabeledFacetTemplateMatch N (normalizedFigureFacetLabel N P v V f F) F
      (normalizedFigureCellLabel P v V f) := by
  dsimp only
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hiF : Facet V (f '' F) := by
    change Facet (vertexFigure P v _) (f '' F)
    rw [← him]
    exact embedding_facet_image f hF
  obtain ⟨K, ⟨hK, hvK, hKF⟩, _⟩ :=
    (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).2 _ hiF
  have hvK' : v ∈ K.extremePoints ℝ := (face_extremePoints_eq hK.1).symm ▸ ⟨hvK, hv⟩
  have hm := unitUniform5_smallFaces_globalFacetLabel
    classification3D classification4D hP hs N hLIB hK
  have ht := unitUniform5_labeled_facet_template hP hK hvK' N hLIB hm
  dsimp only at ht
  rw [hKF] at ht
  have hn : normalizedFigureFacetLabel N P v V f F = globalFacetLabel N K := by
    unfold normalizedFigureFacetLabel
    rw [← hKF]
    exact parentFigureFacetLabel_section (n := 2) hP hv hK.1 hvK N
  change LabeledFacetTemplateMatch N (normalizedFigureFacetLabel N P v V f F) F _
  rw [hn]
  exact labeledFacetTemplateMatch_pullback f N _ F (parentFigureCellLabel P v V) ht

theorem actual_normalized_ridge_template
    {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q H : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hH : IsConvexFace Q H) (hne : H.Nonempty) (hd : affineDimension H = 2) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    Congruent H (cellFigureModel (normalizedFigureCellLabel P v V f H)) := by
  dsimp only
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hiH : IsConvexFace V (f '' H) := by
    change IsConvexFace (vertexFigure P v _) (f '' H)
    rw [← him]
    exact embedding_face_image f hH
  obtain ⟨C, ⟨hC, hvC, hdC, hCH⟩, _⟩ :=
    (unitUniform_vertexFigure_face_correspondence (n := 2) hP hv 2).2 _ hiH (hne.image f)
      (by rwa [affineDimension_affineIsometry_image])
  have hvC' : v ∈ C.extremePoints ℝ := (face_extremePoints_eq hC).symm ▸ ⟨hvC, hv⟩
  have ht := unitUniform5_cell_figure_matches hP hC hdC hvC'
  rw [hCH] at ht
  have hn : normalizedFigureCellLabel P v V f H = globalCellLabel C := by
    unfold normalizedFigureCellLabel
    rw [← hCH]
    exact parentFigureCellLabel_section (n := 2) hP hv hC hvC
  change Congruent H (cellFigureModel (normalizedFigureCellLabel P v V f H))
  rw [hn]
  exact congruent_trans (congruent_affineIsometry_image f H) ht

end Uniform5.Composition
