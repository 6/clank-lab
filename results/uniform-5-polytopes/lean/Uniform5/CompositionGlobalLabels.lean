import Uniform5.CompositionCanonicalCoverage

/-! One geometric label per actual face, shared by every polygon cycle.
Fallback values are never used when a genuine model match exists. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [PseudoMetricSpace E]

noncomputable def globalFacetLabel (N : LibraryNumericalData) (K : Set E) :
    CanonicalFacetName :=
  if h : ∃ n, Congruent K (N.model n) then Classical.choose h
  else canonicalFacetIndex (.wythoff 0 0)

noncomputable def globalCellLabel (C : Set E) : CellType :=
  if h : ∃ c, Congruent C (cellTypeModel c) then Classical.choose h
  else cellType ∅

theorem globalFacetLabel_matches (N : LibraryNumericalData) (K : Set E)
    (h : ∃ n, Congruent K (N.model n)) : Congruent K (N.model (globalFacetLabel N K)) := by
  rw [globalFacetLabel, dif_pos h]
  exact Classical.choose_spec h

theorem globalCellLabel_matches (C : Set E)
    (h : ∃ c, Congruent C (cellTypeModel c)) : Congruent C (cellTypeModel (globalCellLabel C)) := by
  rw [globalCellLabel, dif_pos h]
  exact Classical.choose_spec h

/-- Intrinsic cell labels do not depend on which congruent representative
was supplied by a cycle or by a neighboring facet. -/
theorem globalCellLabel_eq {C : Set E} {c : CellType}
    (hc : Congruent C (cellTypeModel c)) : globalCellLabel C = c := by
  have hg := globalCellLabel_matches C ⟨c, hc⟩
  have he := cellType_eq_iff.mpr (congruent_trans (congruent_symm hg) hc)
  simpa only [cellType_of_model] using he

namespace ActualLibraryCycle
variable {N : LibraryNumericalData} {P G : Set (Space 5)} {k : LibraryPolygonSize}
  (A : ActualLibraryCycle N P G k)

/-- Reuse the actual incidence cycle and all its proved geometry, assigning
names by the whole geometric faces. Shared faces therefore have shared names
even in independently constructed polygon cycles. -/
noncomputable def globallyLabeled : ActualLibraryCycle N P G k :=
  { cycle := A.cycle
    labels :=
      { cellModel := cellTypeModel
        facetModel := N.model
        cellLabel := fun i => globalCellLabel (A.cycle.cell i)
        facetLabel := fun i => globalFacetLabel N (A.cycle.facet i)
        cell_matches := fun i => globalCellLabel_matches _ ⟨A.labels.cellLabel i, by
          simpa only [A.cells] using A.labels.cell_matches i⟩
        facet_matches := fun i => globalFacetLabel_matches N _ ⟨A.labels.facetLabel i, by
          simpa only [A.facets] using A.labels.facet_matches i⟩ }
    geometry := A.geometry
    cells := rfl
    facets := rfl
    closed := congrArg globalCellLabel A.cycle.cell_closed }

@[simp] theorem globallyLabeled_cell (i : ℕ) :
    A.globallyLabeled.labels.cellLabel i = globalCellLabel (A.cycle.cell i) := rfl

@[simp] theorem globallyLabeled_facet (i : Fin A.cycle.length) :
    A.globallyLabeled.labels.facetLabel i = globalFacetLabel N (A.cycle.facet i) := rfl

theorem cellLabel_eq_global (i : ℕ) :
    A.labels.cellLabel i = globalCellLabel (A.cycle.cell i) := by
  apply (globalCellLabel_eq ?_).symm
  simpa only [A.cells] using A.labels.cell_matches i

end ActualLibraryCycle

/-- Actual small-faced polytopes have coherent canonical labels, with
facet coverage derived solely from LIB and the cited classifications. -/
theorem unitUniform5_smallFaces_globalFacetLabel
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    (N : LibraryNumericalData) (hLIB : LIB N) {K : Set (Space 5)} (hK : Facet P K) :
    Congruent K (N.model (globalFacetLabel N K)) :=
  globalFacetLabel_matches N K (unitUniform5_smallFaces_facet_coverage
    classification3D classification4D hP hs N hLIB K hK)

end Uniform5.Composition
