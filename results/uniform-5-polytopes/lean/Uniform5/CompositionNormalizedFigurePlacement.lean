import Uniform5.CompositionNormalizedFaceTemplates
import Uniform5.CompositionFigurePlacement

/-! The prescribed template offset in normalized coordinates follows from
the actual facet-center projection and isometric invariance of distance. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem embedding_infDist_affineSpan (f : E →ᵃⁱ[ℝ] F) (H : Set E) (x : E) :
    Metric.infDist (f x) (affineSpan ℝ (f '' H) : Set F) =
      Metric.infDist x (affineSpan ℝ H : Set E) := by
  change Metric.infDist (f x) (affineSpan ℝ (f.toAffineMap '' H) : Set F) = _
  rw [← AffineSubspace.map_span, AffineSubspace.coe_map]
  exact Metric.infDist_image f.isometry

theorem actual_normalized_facet_offset
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q F : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hf0 : f 0 = vertexCentroid (vertices P (uniform_finitePolytope hP.1)) +
      figureCenter (v - vertexCentroid (vertices P (uniform_finitePolytope hP.1))) (intrinsicRadius P))
    (hF : Facet Q F) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    Metric.infDist (0 : Space 4) (affineSpan ℝ F : Set (Space 4)) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * intrinsicRadius
          (N.model (normalizedFigureFacetLabel N P v V f F)) ^ 2))) ^ 2) := by
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
  have hn : normalizedFigureFacetLabel N P v V f F = globalFacetLabel N K := by
    unfold normalizedFigureFacetLabel
    rw [← hKF]
    exact parentFigureFacetLabel_section (n := 2) hP hv hK.1 hvK N
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd, _⟩ :=
    unitUniform5_facet_figure_placement hP hK hvK'
  rw [hKF, ← hf0, embedding_infDist_affineSpan] at hd
  change Metric.infDist (0 : Space 4) (affineSpan ℝ F : Set (Space 4)) =
    Real.sqrt ((Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))) ^ 2 -
      (Real.sqrt (1 - 1 / (4 * intrinsicRadius
        (N.model (normalizedFigureFacetLabel N P v V f F)) ^ 2))) ^ 2)
  rw [hn, ← intrinsicRadius_cross_congruent hm]
  exact hd

end Uniform5.Composition
