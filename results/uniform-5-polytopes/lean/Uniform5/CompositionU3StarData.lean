import Uniform5.CompositionStageTwoInputs
import Uniform5.CompositionNeighborCandidates

/-! Geometric stars and exact encodings used by the independent stage-three
search. These data carry no search correctness or extension to a uniform
five-polytope. In particular, a complete star need not extend globally. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- One placed whole library facet; the map includes translations. -/
structure U3PlacedFacet where
  name : CanonicalFacetName
  placement : Space 4 →ᵃⁱ[ℝ] Space 5
  figureFace : Set (Space 4)

/-- Untrusted geometric interpretation of an internally enumerated search
state. The JSON report does not serialize these placements. -/
structure U3StarData where
  root : Space 5
  center : Space 5
  radius : ℝ
  figure : StageTwoFigureData
  figureEmbedding : Space 4 →ᵃⁱ[ℝ] Space 5
  facets : List U3PlacedFacet

namespace U3StarData

def facet (N : LibraryNumericalData) (X : U3StarData) (i : Fin X.facets.length) :
    Set (Space 5) :=
  (X.facets.get i).placement '' N.model (X.facets.get i).name

def star (N : LibraryNumericalData) (X : U3StarData) : Set (Set (Space 5)) :=
  Set.range (X.facet N)

def points (N : LibraryNumericalData) (X : U3StarData) : Set (Space 5) :=
  {x | ∃ i, x ∈ (X.facet N i).extremePoints ℝ}

def hull (N : LibraryNumericalData) (X : U3StarData) : Set (Space 5) :=
  convexHull ℝ {x | ∃ F ∈ X.star N, x ∈ F}

end U3StarData

/-- A complete geometric star of a stage-two signature. The whole placed
facets, their section faces, convex placement, sphere and separation are
specified; extendibility to a uniform five-polytope is not required. -/
structure U3GeometricStar (N : LibraryNumericalData) (S : StageOneNumericalData)
    (c : RootRegionClass S) (X : U3StarData) : Prop where
  figure : StageTwoFigureConditions N S c X.radius X.figure
  root_radius : dist X.root X.center = X.radius
  figure_center : X.figureEmbedding 0 =
    X.center + figureCenter (X.root - X.center) X.radius
  facet_faces : ∀ i : Fin X.facets.length, Facet X.figure.carrier (X.facets.get i).figureFace
  facet_labels : ∀ i : Fin X.facets.length,
    (X.facets.get i).name = X.figure.facetLabel (X.facets.get i).figureFace
  facet_injective : Function.Injective (fun i : Fin X.facets.length => (X.facets.get i).figureFace)
  facet_complete : ∀ H, Facet X.figure.carrier H →
    ∃ i : Fin X.facets.length, (X.facets.get i).figureFace = H
  base_vertex : ∀ i : Fin X.facets.length,
    (X.facets.get i).placement (N.baseVertex (X.facets.get i).name) = X.root
  figure_sections : ∀ i : Fin X.facets.length,
    (X.facets.get i).placement '' N.figureModel (X.facets.get i).name =
      X.figureEmbedding '' (X.facets.get i).figureFace
  section_exact : ∀ i : Fin X.facets.length,
    X.facet N i ∩ (X.figureEmbedding '' X.figure.carrier) =
      X.figureEmbedding '' (X.facets.get i).figureFace
  hull_figure : X.figureEmbedding '' X.figure.carrier =
    vertexFigure (X.hull N) X.root X.center
  convex_placement : ∀ i : Fin X.facets.length, Facet (X.hull N) (X.facet N i)
  sphere : ∀ x ∈ X.points N, dist x X.center = X.radius
  separation : ∀ x ∈ X.points N, ∀ y ∈ X.points N, x ≠ y → 1 ≤ dist x y

/-- Exact combinatorial encoding from `canon.encode`: each entry contains a
facet type and its tuple of point identifiers, in the traversal order. -/
abbrev U3Encoding := List (CanonicalFacetName × List ℕ)

/-- Congruence of full stars preserving both the distinguished vertex and
the center. This is stronger than congruence of the vertex figures alone. -/
def U3StarCongruent (N : LibraryNumericalData) (X Y : U3StarData) : Prop :=
  ∃ g : Space 5 ≃ᵃⁱ[ℝ] Space 5,
    g X.root = Y.root ∧ g X.center = Y.center ∧
      facetSetImage g (X.star N) = Y.star N

theorem u3StarCongruent_refl (N : LibraryNumericalData) (X : U3StarData) :
    U3StarCongruent N X X := by
  refine ⟨AffineIsometryEquiv.refl ℝ (Space 5), rfl, rfl, ?_⟩
  ext F
  simp [facetSetImage]

end Uniform5.Composition
