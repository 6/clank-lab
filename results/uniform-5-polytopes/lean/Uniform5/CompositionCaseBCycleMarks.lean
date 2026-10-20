import Uniform5.CompositionCaseBMarkedCycle

/-! The antiprism rays in an actual Case B cycle are uniquely determined. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
open scoped BigOperators

variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- At an antiprism ray both incident slots are right angles, and no slot
has two antiprism ends. -/
theorem antiprism_neighbor_rule (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (i : Fin D.length) :
    ¬ (Congruent (D.cell i) (antiprismModel n) ∧
      Congruent (D.cell (i.val + 1)) (antiprismModel n)) ∧
    ((Congruent (D.cell i) (antiprismModel n) ∨
      Congruent (D.cell (i.val + 1)) (antiprismModel n)) →
      D.wordAngle n i = Real.pi / 2) := by
  have hd (j : ℕ) := unitUniform3_prism_antiprism_disjoint
    (polygonFace_unitPolygon hP hG).1 (D.cell_unitUniform hP hG j)
  rcases D.nonexceptional_slot classification4D hP hG hn i with
    ⟨q, hq, hK, hA, hB, ha⟩ | ⟨hK, hAB, ha⟩
  · constructor
    · rintro ⟨ha, _⟩
      exact hd i hA ha
    · rintro (ha | hb)
      · exact (hd i hA ha).elim
      · exact (hd (i.val + 1) hB hb).elim
  · refine ⟨?_, fun _ => ha⟩
    rintro ⟨hA, hB⟩
    rcases hAB with ⟨_, hp⟩ | ⟨hp, _⟩
    · exact hd (i.val + 1) hp hB
    · exact hd i hp hA

noncomputable def antiprismRayIndices (n : ℕ) : Finset (Fin D.length) := by
  classical
  exact Finset.univ.filter (fun i => Congruent (D.cell i) (antiprismModel n))

/-- At most one actual ray in the full cycle is an antiprism. -/
theorem antiprism_count_le_one (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) :
    (D.antiprismRayIndices n).card ≤ 1 := by
  classical
  unfold antiprismRayIndices
  have hrot (i : Fin D.length) : D.cell (finRotate D.length i) = D.cell (i.val + 1) :=
    cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed i
  apply marked_cycle_count_le_one _ (fun i => D.wordAngle n i)
  · intro i
    have := D.nonexceptional_angle_lower classification4D hP hG hn i
    linarith [Real.pi_pos]
  · intro i
    rw [hrot]
    exact (D.antiprism_neighbor_rule classification4D hP hG hn i).1
  · intro i
    rw [hrot]
    exact (D.antiprism_neighbor_rule classification4D hP hG hn i).2
  · rw [Fin.sum_univ_eq_sum_range]
    exact D.strict_perimeter hP hG

/-- If an antiprism occurs, the actual cycle has exactly three or four rays. -/
theorem antiprism_length_cases (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n)
    (hex : ∃ i : Fin D.length, Congruent (D.cell i) (antiprismModel n)) :
    D.length = 3 ∨ D.length = 4 := by
  classical
  have hrot (i : Fin D.length) : D.cell (finRotate D.length i) = D.cell (i.val + 1) :=
    cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed i
  have hh : D.length ≤ 4 := by
    apply marked_cycle_length_le_four
      (fun i : Fin D.length => Congruent (D.cell i) (antiprismModel n))
      (fun i => D.wordAngle n i)
    · exact D.nonexceptional_angle_lower classification4D hP hG hn
    · intro i
      rw [hrot]
      exact (D.antiprism_neighbor_rule classification4D hP hG hn i).1
    · intro i
      rw [hrot]
      exact (D.antiprism_neighbor_rule classification4D hP hG hn i).2
    · exact hex
    · rw [Fin.sum_univ_eq_sum_range]
      exact D.strict_perimeter hP hG
  have := D.length_ge
  omega

end Uniform5.Composition.ActualPolygonCycle
