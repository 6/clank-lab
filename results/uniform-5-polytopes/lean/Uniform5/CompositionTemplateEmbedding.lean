import Uniform5.CompositionLabeledFigureTemplates

/-! Labeled templates descend through an ambient affine embedding,
preserving every ridge under the same restricted isometry. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem figureTemplateRidge_pullback_image (f : E →ᵃⁱ[ℝ] F)
    {X : Set (Space 4)} {H : Set E} (g : X ≃ᵢ (f '' H)) (C : Set (Space 4)) :
    f '' figureTemplateRidge (g.trans (embeddingSetEquiv f H).symm) C =
      figureTemplateRidge g C := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (embeddingSetEquiv_apply_symm f H (g x)).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(embeddingSetEquiv f H).symm (g x), ⟨x, hx, rfl⟩,
      embeddingSetEquiv_apply_symm f H (g x)⟩

/-- Pullback keeps a single marking isometry for the whole template.
The target ridge label is evaluated on the actual image of that ridge. -/
theorem labeledFacetTemplateMatch_pullback (f : E →ᵃⁱ[ℝ] F)
    (N : LibraryNumericalData) (n : CanonicalFacetName) (H : Set E)
    (labels : Set F → CellType)
    (h : LabeledFacetTemplateMatch N n (f '' H) labels) :
    LabeledFacetTemplateMatch N n H (fun C => labels (f '' C)) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.trans (embeddingSetEquiv f H).symm, ?_⟩
  intro C hC hvC
  dsimp only
  rw [figureTemplateRidge_pullback_image]
  exact hg C hC hvC

end Uniform5.Composition
