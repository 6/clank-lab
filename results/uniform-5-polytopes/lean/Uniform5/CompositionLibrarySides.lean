import Uniform5.CompositionLocalStageOne
import Uniform5.CompositionCycleFilter

/-! Exact facet/polygon/cell sides of semantic cyclic words. Endpoint order
is immaterial, so reversing a cycle preserves every filter requirement. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace CyclicWord
variable {n : ℕ} [NeZero n] {F C : Type*}

noncomputable def HasSide (W : CyclicWord n F C) (f : F) (a b : C) : Prop :=
  ∃ i, W.facet i = f ∧
    ((W.cell i = a ∧ W.cell (finRotate n i) = b) ∨
      (W.cell i = b ∧ W.cell (finRotate n i) = a))

omit [NeZero n] in
theorem hasSide_iff_not_valid (W : CyclicWord n F C) (f : F) (a b : C) :
    W.HasSide f a b ↔
      ¬ W.Valid (fun f' x y => ¬ (f' = f ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))) := by
  classical
  simp only [HasSide, Valid, not_forall, not_not]

theorem hasSide_iff_of_reindex {U V : CyclicWord n F C}
    (h : Relation.EqvGen ReindexStep U V) (f : F) (a b : C) :
    U.HasSide f a b ↔ V.HasSide f a b := by
  rw [hasSide_iff_not_valid, hasSide_iff_not_valid]
  apply not_congr
  apply valid_iff_of_reindex (h := h)
  intro f' x y
  tauto

noncomputable def classHasSide (W : Class n F C) (f : F) (a b : C) : Prop :=
  Quotient.lift (fun V => V.HasSide f a b)
    (fun _ _ h => propext (hasSide_iff_of_reindex h f a b)) W

end CyclicWord

/-- The paper's side (K between Ca and Cb at a p-gon). Both orientations
represent the same incidence and impose the same filter requirement. -/
structure LibraryWordSide where
  polygon : ℕ
  facet : CanonicalFacetName
  left : CellType
  right : CellType

noncomputable def LibraryCycleClass.HasSide (c : LibraryCycleClass) (s : LibraryWordSide) : Prop :=
  c.1.val = s.polygon ∧ CyclicWord.classHasSide c.2.2 s.facet s.left s.right

noncomputable def LibraryCycleWord.sideSet (W : LibraryCycleWord) : Set LibraryWordSide :=
  {s | W.classCode.HasSide s}

theorem LibraryCycleWord.mem_sideSet (W : LibraryCycleWord) (s : LibraryWordSide) :
    s ∈ W.sideSet ↔ W.polygon.val = s.polygon ∧ W.word.HasSide s.facet s.left s.right := Iff.rfl

theorem LibraryCycleWord.sideSet_eq_of_class {U V : LibraryCycleWord}
    (h : U.classCode = V.classCode) : U.sideSet = V.sideSet := by
  unfold sideSet
  rw [h]

/-- Every required side is a genuine incidence in the concrete facet model.
No certificate-provided incidence relation is trusted. -/
noncomputable def libraryFilterIncidence (N : LibraryNumericalData) :
    CycleFilter.Incidence LibraryCycleWord LibraryWordSide CanonicalFacetName where
  sides := LibraryCycleWord.sideSet
  facet := LibraryWordSide.facet
  required f := {s | s.facet = f ∧ ModelPolygonWord (N.model f) s.polygon
    (cellTypeModel s.left) (cellTypeModel s.right)}

theorem admissible_side_required {N : LibraryNumericalData} {W : LibraryCycleWord}
    (hW : W.Admissible N) {s : LibraryWordSide} (hs : s ∈ W.sideSet) :
    s ∈ (libraryFilterIncidence N).required s.facet := by
  obtain ⟨hk, i, hf, hp⟩ := W.mem_sideSet s |>.mp hs
  refine ⟨rfl, ?_⟩
  have h := hW.1 i
  change ModelPolygonWord (N.model (W.word.facet i)) W.polygon.val
    (cellTypeModel (W.word.cell i)) (cellTypeModel (W.word.cell (finRotate W.length.val i))) at h
  rcases hp with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [hf, ha, hb] at h
    simpa only [hk] using h
  · rw [hf, ha, hb] at h
    have h' := modelPolygonWord_swap h
    simpa only [hk] using h'

end Uniform5.Composition
