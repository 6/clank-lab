import Uniform5.CompositionU3StarData

/-! Exact whole-star congruence carries the hull and its actual vertex
figure section. This supplies the geometric link used by the DEV input. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem u3Star_hull_image {N : LibraryNumericalData} {X Y : U3StarData}
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hs : facetSetImage g (X.star N) = Y.star N) :
    g '' X.hull N = Y.hull N := by
  have hu : g '' {x | ∃ F ∈ X.star N, x ∈ F} =
      {x | ∃ F ∈ Y.star N, x ∈ F} := by
    rw [← hs]
    ext x
    constructor
    · rintro ⟨y, ⟨F, hF, hy⟩, rfl⟩
      exact ⟨g '' F, ⟨F, hF, rfl⟩, ⟨y, hy, rfl⟩⟩
    · rintro ⟨F, ⟨A, hA, rfl⟩, ⟨y, hy, rfl⟩⟩
      exact ⟨y, ⟨A, hA, hy⟩, rfl⟩
  change g '' convexHull ℝ _ = convexHull ℝ _
  calc
    g '' convexHull ℝ {x | ∃ F ∈ X.star N, x ∈ F} =
        convexHull ℝ (g '' {x | ∃ F ∈ X.star N, x ∈ F}) :=
      g.toAffineMap.image_convexHull _
    _ = _ := congrArg (convexHull ℝ) hu

/-- Congruence of full stars with the prescribed center and root implies
congruence of their genuine four-dimensional vertex figures. -/
theorem U3StarCongruent.figure_congruent
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {c d : RootRegionClass S} {X Y : U3StarData}
    (hX : U3GeometricStar N S c X) (hY : U3GeometricStar N S d Y)
    (h : U3StarCongruent N X Y) : Congruent X.figure.carrier Y.figure.carrier := by
  obtain ⟨g, hr, hc, hs⟩ := h
  have he : g '' (X.figureEmbedding '' X.figure.carrier) =
      Y.figureEmbedding '' Y.figure.carrier := by
    rw [hX.hull_figure, hY.hull_figure, vertexFigure_image,
      u3Star_hull_image g hs, hr, hc]
  have hi : Congruent (X.figureEmbedding '' X.figure.carrier)
      (Y.figureEmbedding '' Y.figure.carrier) := by
    rw [← he]
    exact congruent_affineIsometryEquiv_image g _
  exact congruent_trans (congruent_affineIsometry_image X.figureEmbedding _)
    (congruent_trans hi (congruent_symm (congruent_affineIsometry_image Y.figureEmbedding _)))

end Uniform5.Composition
