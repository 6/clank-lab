import Uniform5.CompositionLabeledCycle
import Uniform5.CompositionCycleQuotient

/-! Actual model coverage constructs a closed word, including at its seam. -/
noncomputable section
namespace Uniform5.Composition
open Set

instance ActualPolygonCycle.length_neZero {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) : NeZero D.length :=
  ⟨by have := D.length_ge; omega⟩

theorem exists_closed_cycleModelLabels {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) {Cell FacetName : Type*}
    (C : Cell → Set (Space 3)) (F : FacetName → Set (Space 4))
    (hC : ∀ K ∈ Set.range D.cell, ∃ c, Congruent K (C c))
    (hF : ∀ i, ∃ f, Congruent (D.facet i) (F f)) :
    ∃ L : CycleModelLabels D Cell FacetName,
      L.cellModel = C ∧ L.facetModel = F ∧ L.cellLabel D.length = L.cellLabel 0 := by
  classical
  let label : Set.range D.cell → Cell := fun K => Classical.choose (hC K K.property)
  let L : CycleModelLabels D Cell FacetName :=
    { cellModel := C
      facetModel := F
      cellLabel := fun i => label ⟨D.cell i, ⟨i, rfl⟩⟩
      facetLabel := fun i => Classical.choose (hF i)
      cell_matches := fun i => Classical.choose_spec (hC (D.cell i) ⟨i, rfl⟩)
      facet_matches := fun i => Classical.choose_spec (hF i) }
  refine ⟨L, rfl, rfl, ?_⟩
  exact congrArg label (Subtype.ext D.cell_closed)

namespace CycleModelLabels
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {Cell FacetName : Type*}
  (L : CycleModelLabels D Cell FacetName)

noncomputable def cyclicWord : CyclicWord D.length FacetName Cell :=
  ⟨L.facetLabel, fun i => L.cellLabel i⟩

theorem cyclicWord_valid (hclosed : L.cellLabel D.length = L.cellLabel 0)
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    L.cyclicWord.Valid (fun f a b => ModelPolygonWord (L.facetModel f) k
      (L.cellModel a) (L.cellModel b)) := by
  intro i
  change ModelPolygonWord (L.facetModel (L.facetLabel i)) k
    (L.cellModel (L.cellLabel i)) (L.cellModel (L.cellLabel (finRotate D.length i)))
  rw [cycle_apply_finRotate (by have := D.length_ge; omega) L.cellLabel hclosed]
  exact L.word_occurs hP hG i

theorem cyclicWord_closure (hclosed : L.cellLabel D.length = L.cellLabel 0)
    (k : ℕ) (s : ℝ) :
    L.cyclicWord.closure k (intrinsicRadius ∘ L.facetModel)
      (intrinsicRadius ∘ L.cellModel) s =
      cycleClosureFunction D.length (unitPolygonRadius k) (L.height k) (L.angle k) s := by
  have hn : 2 ≤ D.length := by have := D.length_ge; omega
  have hheight : L.height k D.length = L.height k 0 := by
    unfold height
    rw [hclosed]
  unfold CyclicWord.closure finiteWordClosure
  have hang : (fun i : Fin D.length => facetWordAngle k
      ((intrinsicRadius ∘ L.facetModel ∘ L.cyclicWord.facet) i)
      ((intrinsicRadius ∘ L.cellModel ∘ L.cyclicWord.cell) i)
      ((intrinsicRadius ∘ L.cellModel ∘ L.cyclicWord.cell) (finRotate D.length i))) =
      fun i : Fin D.length => L.angle k i := by
    funext i
    simp only [cyclicWord, Function.comp_apply]
    rw [cycle_apply_finRotate hn L.cellLabel hclosed]
    simp only [angle, dif_pos i.isLt]
  dsimp only [Function.comp_apply] at hang ⊢
  rw [hang]
  exact finiteCycleClosure_eq hn (unitPolygonRadius k) (L.height k) (L.angle k) hheight s

theorem cyclicWord_actual_root (hclosed : L.cellLabel D.length = L.cellLabel 0)
    {k : ℕ} (hD : D.Stage1Geometry k) :
    L.cyclicWord.closure k (intrinsicRadius ∘ L.facetModel)
      (intrinsicRadius ∘ L.cellModel) (1 / intrinsicRadius P) = 0 := by
  rw [L.cyclicWord_closure hclosed]
  exact (L.geometric_properties hD).2.2

end CycleModelLabels
end Uniform5.Composition
