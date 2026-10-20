import Uniform5.CompositionActualCycleData
import Uniform5.CompositionModelIncidence

/-! Exact model labels preserve an actual cycle's incidence and metrics. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- A label names an actual congruent model. Merely assigning integers or
matching approximate radii is insufficient to construct this data. -/
structure CycleModelLabels {P G : Set (Space 5)} (D : ActualPolygonCycle P G)
    (Cell FacetName : Type*) where
  cellModel : Cell → Set (Space 3)
  facetModel : FacetName → Set (Space 4)
  cellLabel : ℕ → Cell
  facetLabel : Fin D.length → FacetName
  cell_matches : ∀ i, Congruent (D.cell i) (cellModel (cellLabel i))
  facet_matches : ∀ i, Congruent (D.facet i) (facetModel (facetLabel i))

namespace CycleModelLabels
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {Cell FacetName : Type*}
  (L : CycleModelLabels D Cell FacetName)

noncomputable def height (k : ℕ) (i : ℕ) : ℝ :=
  Real.sqrt ((intrinsicRadius (L.cellModel (L.cellLabel i))) ^ 2 - (unitPolygonRadius k) ^ 2)

noncomputable def angle (k : ℕ) (i : ℕ) : ℝ :=
  if hi : i < D.length then facetWordAngle k (intrinsicRadius (L.facetModel (L.facetLabel ⟨i, hi⟩)))
    (intrinsicRadius (L.cellModel (L.cellLabel i)))
    (intrinsicRadius (L.cellModel (L.cellLabel (i + 1)))) else 0

theorem height_eq (k : ℕ) : L.height k = D.height k := by
  funext i
  unfold height ActualPolygonCycle.height
  rw [← intrinsicRadius_cross_congruent (L.cell_matches i)]

theorem angle_eq (k : ℕ) : L.angle k = D.wordAngle k := by
  funext i
  unfold angle ActualPolygonCycle.wordAngle
  split_ifs with hi
  · rw [← intrinsicRadius_cross_congruent (L.facet_matches ⟨i, hi⟩),
      ← intrinsicRadius_cross_congruent (L.cell_matches i),
      ← intrinsicRadius_cross_congruent (L.cell_matches (i + 1))]
  · rfl

/-- Labels carry the actual polygon occurrence, not only its metric word. -/
theorem word_occurs (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    (i : Fin D.length) :
    ModelPolygonWord (L.facetModel (L.facetLabel i)) k
      (L.cellModel (L.cellLabel i)) (L.cellModel (L.cellLabel (i.val + 1))) := by
  have hGi : PolygonFace (D.facet i) G k :=
    ⟨face_restrict hG.1 (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  have hCA : Facet (D.facet i) (D.cell i) :=
    ⟨face_restrict (D.cell_face i) (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.2.1,
      (polygonFace_nonempty hG).mono (D.cell_contains i), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP i).1]⟩
  have hCB : Facet (D.facet i) (D.cell (i.val + 1)) :=
    ⟨face_restrict (D.cell_face (i.val + 1)) (D.facet_incidence i).1.1.2.1
        (D.facet_incidence i).2.2.2,
      (polygonFace_nonempty hG).mono (D.cell_contains (i.val + 1)), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP i).1]⟩
  exact modelPolygonWord_of_actual (D.facet_unitUniform hP i) hGi hCA hCB
    (D.cell_contains i) (D.cell_contains (i.val + 1))
    (cell_cycle_consecutive_ne D.length_ge D.cell D.cell_closed D.cell_injective i.isLt)
    (L.facet_matches i) (L.cell_matches i) (L.cell_matches (i.val + 1))

/-- Model-word closure, perimeter and domain follow by exact radius
transport; there is no comparison by interval overlap. -/
theorem geometric_properties {k : ℕ} (hD : D.Stage1Geometry k) :
    (∑ i ∈ Finset.range D.length, L.angle k i) < 2 * Real.pi ∧
      ClosureDomain D.length (unitPolygonRadius k) (L.height k) (L.angle k)
        (1 / intrinsicRadius P) ∧
      cycleClosureFunction D.length (unitPolygonRadius k) (L.height k) (L.angle k)
        (1 / intrinsicRadius P) = 0 := by
  rw [L.height_eq, L.angle_eq]
  exact ⟨hD.perimeter, hD.domain, hD.closure⟩

/-- Sound lower angle enclosures cannot prune the cycle of an actual
polygon by the stage-1 test that the lower sum exceeds a full turn. -/
theorem lower_angle_sum_lt {k : ℕ} (hD : D.Stage1Geometry k)
    (lower : ℕ → ℝ) (hlo : ∀ i < D.length, lower i ≤ L.angle k i) :
    (∑ i ∈ Finset.range D.length, lower i) < 2 * Real.pi := by
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun i hi => hlo i (Finset.mem_range.mp hi)))
  exact (L.geometric_properties hD).1

end CycleModelLabels
end Uniform5.Composition
