import Uniform5.CompositionFigureFaceOrder
import Uniform5.CompositionGlobalLabels

/-! Coherent labels on an actual vertex figure, recovered from its actual
parent faces by the proved injectivity of vertex sections. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def parentFaceFromSection (P : Set E) (v : E) (Q H : Set E) : Set E :=
  if h : ∃ F, IsConvexFace P F ∧ v ∈ F ∧ F ∩ Q = H then Classical.choose h else ∅

/-- Taking a section and recovering its parent returns the original actual
face, independently of every choice used in constructing a cycle. -/
theorem unitUniform_parentFaceFromSection {n : ℕ} {P C : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hC : IsConvexFace P C) (hvC : v ∈ C) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    parentFaceFromSection P v Q (C ∩ Q) = C := by
  dsimp only
  let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hex : ∃ F, IsConvexFace P F ∧ v ∈ F ∧ F ∩ Q = C ∩ Q := ⟨C, hC, hvC, rfl⟩
  rw [parentFaceFromSection, dif_pos hex]
  obtain ⟨hF, hvF, he⟩ := Classical.choose_spec hex
  exact ((unitUniform_vertexFigure_section_subset_iff hP hv hF hC hvF hvC).mp he.subset).antisymm
    ((unitUniform_vertexFigure_section_subset_iff hP hv hC hF hvC hvF).mp he.symm.subset)

noncomputable def parentFigureFacetLabel (N : LibraryNumericalData)
    (P : Set E) (v : E) (Q H : Set E) : CanonicalFacetName :=
  globalFacetLabel N (parentFaceFromSection P v Q H)

noncomputable def parentFigureCellLabel (P : Set E) (v : E) (Q H : Set E) : CellType :=
  globalCellLabel (parentFaceFromSection P v Q H)

theorem parentFigureFacetLabel_section {n : ℕ} {P C : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hC : IsConvexFace P C) (hvC : v ∈ C) (N : LibraryNumericalData) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    parentFigureFacetLabel N P v Q (C ∩ Q) = globalFacetLabel N C := by
  dsimp only [parentFigureFacetLabel]
  rw [unitUniform_parentFaceFromSection hP hv hC hvC]

theorem parentFigureCellLabel_section {n : ℕ} {P C : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hC : IsConvexFace P C) (hvC : v ∈ C) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    parentFigureCellLabel P v Q (C ∩ Q) = globalCellLabel C := by
  dsimp only [parentFigureCellLabel]
  rw [unitUniform_parentFaceFromSection hP hv hC hvC]

end Uniform5.Composition
