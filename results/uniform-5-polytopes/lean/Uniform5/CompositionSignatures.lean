import Uniform5.CompositionReciprocalClassHull

/-! Literal stage-two signatures. Facets and edges are counted as actual
geometric faces; equal labels retain their multiplicity. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The two multisets in the paper's definition of a vertex-figure signature.
An edge word includes its original polygon size and its cyclic word modulo
rotation and reversal. This data does not assert uniqueness of realization. -/
structure VertexFigureSignature where
  facets : Multiset CanonicalFacetName
  edges : Multiset LibraryCycleClass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All nonempty actual faces of a specified affine dimension. -/
noncomputable def facesOfDimension (P : Set E) (hP : FinitePolytope P) (d : ℕ) :
    Finset (Set E) := by
  classical
  exact (finitePolytope_faces_finite hP).toFinset.filter fun F =>
    F.Nonempty ∧ affineDimension F = d

theorem mem_facesOfDimension {P F : Set E} (hP : FinitePolytope P) (d : ℕ) :
    F ∈ facesOfDimension P hP d ↔
      IsConvexFace P F ∧ F.Nonempty ∧ affineDimension F = d := by
  classical
  simp only [facesOfDimension, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- Label functions are read only on the actual facets and actual edges.
Their geometric validity is a separate condition in the S2 interface. -/
noncomputable def geometricFigureSignature (P : Set E) (hP : FinitePolytope P)
    (facetLabel : Set E → CanonicalFacetName)
    (edgeWord : Set E → LibraryCycleClass) : VertexFigureSignature where
  facets := (facesOfDimension P hP 3).val.map facetLabel
  edges := (facesOfDimension P hP 1).val.map edgeWord

theorem geometricFigureSignature_facet_card (P : Set E) (hP : FinitePolytope P)
    (f : Set E → CanonicalFacetName) (w : Set E → LibraryCycleClass) :
    (geometricFigureSignature P hP f w).facets.card = (facesOfDimension P hP 3).card := by
  simp [geometricFigureSignature]

theorem geometricFigureSignature_edge_card (P : Set E) (hP : FinitePolytope P)
    (f : Set E → CanonicalFacetName) (w : Set E → LibraryCycleClass) :
    (geometricFigureSignature P hP f w).edges.card = (facesOfDimension P hP 1).card := by
  simp [geometricFigureSignature]

/-- Repeated facet types remain repeated in a signature. -/
theorem signature_repeated_facet_card (f : CanonicalFacetName) :
    (VertexFigureSignature.mk {f, f} 0).facets.card = 2 := by simp

/-- Raw signature output only. Coverage, counts, and geometric validity
are not supplied by the data type. -/
structure StageTwoNumericalData (S : StageOneNumericalData) where
  signatures : ActiveRootClass S → Finset VertexFigureSignature

/-- The closure equations belonging to all edge words of a signature.
This is a predicate, not an extra computed input. -/
noncomputable def VertexFigureSignature.RadiusCompatible (σ : VertexFigureSignature)
    (N : LibraryNumericalData) (R : ℝ) : Prop :=
  ∀ W ∈ σ.edges, W.closure N (1 / R) = 0

end Uniform5.Composition
