import Uniform5.CompositionFigureParentLabels

/-! The single facet and cell label maps on an intrinsic coordinate model
of an actual parent vertex figure. -/
noncomputable section
namespace Uniform5.Composition

noncomputable def normalizedFigureFacetLabel (N : LibraryNumericalData)
    (P : Set (Space 5)) (v : Space 5) (V : Set (Space 5))
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (H : Set (Space 4)) : CanonicalFacetName :=
  parentFigureFacetLabel N P v V (f '' H)

noncomputable def normalizedFigureCellLabel
    (P : Set (Space 5)) (v : Space 5) (V : Set (Space 5))
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (H : Set (Space 4)) : CellType :=
  parentFigureCellLabel P v V (f '' H)

end Uniform5.Composition
