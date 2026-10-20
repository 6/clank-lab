import Uniform5.CompositionCaseBFamilyAngles
import Uniform5.CaseBAngles

/-! The actual polygon cycle supplies the Case B facet types and their exact angles. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set

variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- The two cells recorded at a cycle slot are distinct actual facets of its facet. -/
theorem slot_incidence (hP : UnitUniform 5 P) {n : ℕ} (hG : PolygonFace P G n)
    (i : Fin D.length) :
    PolygonFace (D.facet i) G n ∧ Facet (D.facet i) (D.cell i) ∧
      Facet (D.facet i) (D.cell (i.val + 1)) ∧ D.cell i ≠ D.cell (i.val + 1) := by
  refine ⟨polygonFace_restrict_parent hG (D.facet_incidence i).1.1.2.1
    (D.facet_incidence i).2.1, ?_, ?_, ?_⟩
  · exact ⟨face_restrict (D.cell_face i) (D.facet_incidence i).1.1.2.1
      (D.facet_incidence i).2.2.1,
      (polygonFace_nonempty hG).mono (D.cell_contains i), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP i).1]⟩
  · exact ⟨face_restrict (D.cell_face (i.val + 1)) (D.facet_incidence i).1.1.2.1
      (D.facet_incidence i).2.2.2,
      (polygonFace_nonempty hG).mono (D.cell_contains (i.val + 1)), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP i).1]⟩
  · exact cell_cycle_consecutive_ne D.length_ge D.cell D.cell_closed D.cell_injective i.isLt

/-- An actual duoprism slot has two prism rays and the regular polygon angle. -/
theorem duoprism_slot {n q : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (hq : 3 ≤ q) (i : Fin D.length)
    (hK : Congruent (D.facet i) (duoprismModel n q)) :
    Congruent (D.cell i) (polygonPrismModel n) ∧
      Congruent (D.cell (i.val + 1)) (polygonPrismModel n) ∧
      D.wordAngle n i = Real.pi * (1 - 2 / (q : ℝ)) := by
  obtain ⟨hGi, hA, hB, hAB⟩ := D.slot_incidence hP hG i
  have hn := (polygonFace_unitPolygon hP hG).1
  have hc := unitUniform4_duoprism_word_cells hn hq hn4 (D.facet_unitUniform hP i)
    hGi hA hB (D.cell_contains i) (D.cell_contains (i.val + 1)) hAB hK
  refine ⟨hc.1, hc.2, ?_⟩
  rw [wordAngle, dif_pos i.isLt]
  exact unitUniform4_duoprism_word_angle hn hq hn4 (D.facet_unitUniform hP i)
    hGi hA hB (D.cell_contains i) (D.cell_contains (i.val + 1)) hAB hK

/-- An actual antiprism-prism slot has one ray of each type and a right angle. -/
theorem antiprismPrism_slot {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (i : Fin D.length)
    (hK : Congruent (D.facet i) (antiprismPrismModel n)) :
    ((Congruent (D.cell i) (antiprismModel n) ∧
      Congruent (D.cell (i.val + 1)) (polygonPrismModel n)) ∨
      (Congruent (D.cell i) (polygonPrismModel n) ∧
      Congruent (D.cell (i.val + 1)) (antiprismModel n))) ∧
      D.wordAngle n i = Real.pi / 2 := by
  obtain ⟨hGi, hA, hB, hAB⟩ := D.slot_incidence hP hG i
  have hn := (polygonFace_unitPolygon hP hG).1
  refine ⟨unitUniform4_antiprismPrism_word_cells hn hn4 (D.facet_unitUniform hP i)
    hGi hA hB (D.cell_contains i) (D.cell_contains (i.val + 1)) hAB hK, ?_⟩
  rw [wordAngle, dif_pos i.isLt]
  exact unitUniform4_antiprismPrism_word_angle hn hn4 (D.facet_unitUniform hP i)
    hGi hA hB (D.cell_contains i) (D.cell_contains (i.val + 1)) hAB hK

/-- The cited four-dimensional classification yields exact local metric alternatives
at every slot, retaining the original polygon parameter. -/
theorem nonexceptional_slot (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (i : Fin D.length) :
    (∃ q : ℕ, 3 ≤ q ∧ Congruent (D.facet i) (duoprismModel n q) ∧
      Congruent (D.cell i) (polygonPrismModel n) ∧
      Congruent (D.cell (i.val + 1)) (polygonPrismModel n) ∧
      D.wordAngle n i = Real.pi * (1 - 2 / (q : ℝ))) ∨
    (Congruent (D.facet i) (antiprismPrismModel n) ∧
      ((Congruent (D.cell i) (antiprismModel n) ∧
        Congruent (D.cell (i.val + 1)) (polygonPrismModel n)) ∨
       (Congruent (D.cell i) (polygonPrismModel n) ∧
        Congruent (D.cell (i.val + 1)) (antiprismModel n))) ∧
      D.wordAngle n i = Real.pi / 2) := by
  have hn4 : n ≠ 4 := by
    intro he
    apply hn
    simp [CaseB.ExceptionalPolygon, he]
  obtain h | h := unitUniform4_nonexceptional_polygon_family classification4D
    (D.facet_unitUniform hP i) (D.slot_incidence hP hG i).1 hn
  · obtain ⟨q, hq, hK⟩ := h
    exact Or.inl ⟨q, hq, hK, D.duoprism_slot hP hG hn4 hq i hK⟩
  · exact Or.inr ⟨h, D.antiprismPrism_slot hP hG hn4 i h⟩

/-- Every nonexceptional slot consumes at least one third of pi. -/
theorem nonexceptional_angle_lower (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (i : Fin D.length) :
    Real.pi / 3 ≤ D.wordAngle n i := by
  rcases D.nonexceptional_slot classification4D hP hG hn i with
    ⟨q, hq, _, _, _, ha⟩ | ⟨_, _, ha⟩
  · rw [ha]
    have h := CaseB.polygon_angle_lower hq
    nlinarith [Real.pi_pos]
  · rw [ha]
    linarith [Real.pi_pos]

/-- Strict convexity bounds the actual number of rays by five. -/
theorem nonexceptional_length_le_five (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) : D.length ≤ 5 := by
  have hlo : (D.length : ℝ) * (Real.pi / 3) ≤
      ∑ i ∈ Finset.range D.length, D.wordAngle n i := by
    calc
      (D.length : ℝ) * (Real.pi / 3) =
          ∑ _i ∈ Finset.range D.length, Real.pi / 3 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        D.nonexceptional_angle_lower classification4D hP hG hn ⟨i, Finset.mem_range.mp hi⟩)
  have hhi := D.strict_perimeter hP hG
  by_contra h
  have hlen : (6 : ℝ) ≤ D.length := by exact_mod_cast (show 6 ≤ D.length by omega)
  nlinarith [Real.pi_pos]

end Uniform5.Composition.ActualPolygonCycle
