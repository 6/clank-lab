import Uniform5.CompositionPolygonBoundary
import Uniform5.CompositionFigureModelTransport
import Uniform5.CompositionCellTypes

/-! The named RIDGES input (paper, computation `comp:ridges`). Raw finite
lists specify point sets, cyclic orders, and whole-cell labels for each of
the 181 canonical model vertex figures. Correctness and completeness are
the hypothesis; no model uniformity or search-branch coverage is included.
The contextual total of 823 ridges is not part of the stated computation. -/

noncomputable section
namespace Uniform5.Composition
open Set

/-- One raw listed ridge. Its ordered point list is independent of any
claim that it is a polygon, a face, or the figure of the indicated cell. -/
structure ModelRidgeEntry where
  length : ℕ
  point : Fin length → Space 4
  cellLabel : CellType

noncomputable def ModelRidgeEntry.hull (r : ModelRidgeEntry) : Set (Space 4) :=
  convexHull ℝ (Set.range r.point)

/-- The finite ridge lists indexed by the concrete canonical facet names. -/
structure RidgeListData where
  ridges : CanonicalFacetName → List ModelRidgeEntry

/-- Computation RIDGES: the lists of actual 2-faces of the model vertex
figures, their point sets and cyclic orders, and their whole-cell labels
are correct and complete. A label identifies the original three-dimensional
cell, not merely the shape of its two-dimensional vertex figure. -/
structure RIDGES (N : LibraryNumericalData) (D : RidgeListData) : Prop where
  correct : ∀ k, ∀ r ∈ D.ridges k,
    IsConvexFace (N.figureModel k) r.hull ∧
    CyclicPolygonBoundary r.hull r.point ∧
    ∃ C, Facet (N.model k) C ∧ N.baseVertex k ∈ C ∧
      C ∩ N.figureModel k = r.hull ∧ Congruent C (cellTypeModel r.cellLabel)
  complete : ∀ k H, IsConvexFace (N.figureModel k) H → H.Nonempty →
    affineDimension H = 2 → ∃ r ∈ D.ridges k, r.hull = H

namespace RIDGES
variable {N : LibraryNumericalData} {D : RidgeListData} (h : RIDGES N D)
include h

/-- The listed points are exactly the actual vertices of the listed face. -/
theorem points_exact {k : CanonicalFacetName} {r : ModelRidgeEntry}
    (hr : r ∈ D.ridges k) : Set.range r.point = r.hull.extremePoints ℝ :=
  (h.correct k r hr).2.1.vertices

/-- Every listed ridge is an actual nonempty two-dimensional face. -/
theorem listed_face {k : CanonicalFacetName} {r : ModelRidgeEntry}
    (hr : r ∈ D.ridges k) :
    IsConvexFace (N.figureModel k) r.hull ∧ r.hull.Nonempty ∧
      affineDimension r.hull = 2 := by
  obtain ⟨hf, hb, _⟩ := h.correct k r hr
  exact ⟨hf, hb.nonempty, hb.dimension⟩

/-- Every actual ridge has a listed cyclic boundary and a correct whole-cell
label, without a choice of producer branch or a realization assumption. -/
theorem actual_ridge {k : CanonicalFacetName} {H : Set (Space 4)}
    (hH : IsConvexFace (N.figureModel k) H) (hne : H.Nonempty)
    (hd : affineDimension H = 2) :
    ∃ r ∈ D.ridges k, r.hull = H ∧ CyclicPolygonBoundary H r.point ∧
      ∃ C, Facet (N.model k) C ∧ N.baseVertex k ∈ C ∧
        C ∩ N.figureModel k = H ∧ Congruent C (cellTypeModel r.cellLabel) := by
  obtain ⟨r, hr, he⟩ := h.complete k H hH hne hd
  obtain ⟨_, hb, hC⟩ := h.correct k r hr
  refine ⟨r, hr, he, ?_, ?_⟩
  · exact he ▸ hb
  · exact he ▸ hC

end RIDGES
end Uniform5.Composition
