import Uniform5.CompositionWedgeActualHalfspaces

/-! Actual faces are determined by the root and a full facet neighbor
set. This is the whole-face identification used in the paired partition. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem facet_subset_face_of_figure_vertices {P K F : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hF : IsConvexFace P F)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K) (hvF : v ∈ F)
    (hvertices : (K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ ⊆ F) :
    K ⊆ F := by
  let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hvK' : v ∈ K.extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨hvK, hv⟩
  have hplace := unitUniform5_facet_figure_placement hP hK hvK'
  have hfinite : FinitePolytope (K ∩ Q) :=
    finitePolytope_face hplace.1 hplace.2.2.1.1 hplace.2.2.1.2.1
  have hQF : K ∩ Q ⊆ F := by
    rw [finitePolytope_eq_convexHull_extremePoints hfinite]
    exact convexHull_min hvertices hF.1
  have hspan : affineSpan ℝ K ≤ affineSpan ℝ F := by
    rw [← actual_facet_root_figure_span hP hK hv hvK]
    apply affineSpan_mono ℝ
    exact Set.insert_subset hvF hQF
  intro x hx
  rw [← face_affineSpan_inter hF ⟨v, hvF⟩]
  exact ⟨hK.1.2.1 hx, hspan (subset_affineSpan ℝ K hx)⟩

/-- For two facets the same containment forces equality by dimension. -/
theorem facets_eq_of_figure_vertices {P K F : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hF : Facet P F)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K) (hvF : v ∈ F)
    (hvertices : (K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ ⊆ F) :
    K = F := by
  have hKF := facet_subset_face_of_figure_vertices hP hK hF.1 hv hvK hvF hvertices
  apply convexFace_eq_of_dimension_eq (face_restrict hK.1 hF.1.2.1 hKF) hK.2.1
  have hk := hK.2.2
  have hf := hF.2.2
  omega

end Uniform5.Composition
