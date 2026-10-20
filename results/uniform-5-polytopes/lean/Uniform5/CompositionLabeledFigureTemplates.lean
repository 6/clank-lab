import Uniform5.CompositionFacetTemplateTransport
import Uniform5.CompositionFigureParentLabels

/-! Marked facet templates: the isometry carries the whole figure and
every cell's figure ridge, with one shared label function on the target. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def embeddingSetEquivOfImage (f : E →ᵃⁱ[ℝ] F) (P : Set E)
    (Q : Set F) (h : f '' P = Q) : P ≃ᵢ Q := h ▸ embeddingSetEquiv f P

@[simp] theorem embeddingSetEquivOfImage_apply (f : E →ᵃⁱ[ℝ] F) (P : Set E)
    (Q : Set F) (h : f '' P = Q) (x : P) :
    (embeddingSetEquivOfImage f P Q h x : F) = f x := by
  subst Q
  rfl

noncomputable def figureTemplateRidge {X : Set E} {H : Set F}
    (g : X ≃ᵢ H) (C : Set E) : Set F :=
  (fun x : X => (g x : F)) '' {x | (x : E) ∈ C}

theorem figureTemplateRidge_embedding (f : E →ᵃⁱ[ℝ] F) (X C : Set E)
    (H : Set F) (h : f '' X = H) :
    figureTemplateRidge (embeddingSetEquivOfImage f X H h) C = f '' (C ∩ X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx, x.property⟩, (embeddingSetEquivOfImage_apply f X H h x).symm⟩
  · rintro ⟨x, ⟨hxC, hxX⟩, rfl⟩
    exact ⟨⟨x, hxX⟩, hxC, embeddingSetEquivOfImage_apply f X H h ⟨x, hxX⟩⟩

/-- A copy of the facet figure with the original whole-cell labels on its
ridges. This does not replace cell identity by equality of ridge shapes. -/
noncomputable def LabeledFacetTemplateMatch (N : LibraryNumericalData)
    (n : CanonicalFacetName) (H : Set E) (cellLabel : Set E → CellType) : Prop :=
  ∃ g : N.figureModel n ≃ᵢ H,
    ∀ C, Facet (N.model n) C → N.baseVertex n ∈ C →
      Congruent C (cellTypeModel (cellLabel (figureTemplateRidge g C)))

theorem unitUniform5_labeled_facet_template {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ K.extremePoints ℝ) (N : LibraryNumericalData) (hLIB : LIB N)
    {n : CanonicalFacetName} (hn : Congruent K (N.model n)) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    LabeledFacetTemplateMatch N n (K ∩ Q) (parentFigureCellLabel P v Q) := by
  dsimp only
  obtain ⟨f, hf, hfv, hfig, hcells⟩ := unitUniform5_facet_template_embedding hP hK hv N hLIB hn
  refine ⟨embeddingSetEquivOfImage f _ _ hfig, ?_⟩
  intro C hC hvC
  obtain ⟨hCP, _, he, hm⟩ := hcells C hC hvC
  rw [figureTemplateRidge_embedding, he]
  have hvP := hK.1.2.extremePoints_subset_extremePoints hv
  have hvfC : v ∈ f '' C := hfv ▸ mem_image_of_mem f hvC
  rw [parentFigureCellLabel_section (n := 2) hP hvP hCP hvfC]
  exact hm

end Uniform5.Composition
