import Uniform5.CompositionCaseBCycleMarks

/-! Removing the two right-angle slots leaves the exact duoprism tail. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set Classical
open scoped BigOperators
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

noncomputable def slotsAwayFrom (a : Fin D.length) : Finset (Fin D.length) :=
  Finset.univ \ {a, (finRotate D.length).symm a}

theorem predecessor_ne (a : Fin D.length) : (finRotate D.length).symm a ≠ a := by
  intro h
  have hh := congrArg (finRotate D.length) h
  simp only [Equiv.apply_symm_apply] at hh
  exact (finRotate_ne_and_twice_ne D.length_ge a).1 hh.symm

theorem slotsAwayFrom_card (a : Fin D.length) :
    (D.slotsAwayFrom a).card = D.length - 2 := by
  rw [slotsAwayFrom, Finset.card_sdiff (Finset.subset_univ _)]
  simp [D.predecessor_ne a, (D.predecessor_ne a).symm]

theorem slotsAwayFrom_mem (a i : Fin D.length) :
    i ∈ D.slotsAwayFrom a ↔ i ≠ a ∧ finRotate D.length i ≠ a := by
  simp only [slotsAwayFrom, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_and, not_or]
  exact and_congr_right (fun _ => not_congr (finRotate D.length).eq_symm_apply)

/-- The one antiprism ray determines exactly the two right-angle facets. -/
theorem antiprism_slot_partition (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (a : Fin D.length)
    (ha : Congruent (D.cell a) (antiprismModel n)) :
    (∀ i : Fin D.length, Congruent (D.cell i) (antiprismModel n) ↔ i = a) ∧
    (∀ i : Fin D.length, i ∉ D.slotsAwayFrom a →
      Congruent (D.facet i) (antiprismPrismModel n) ∧ D.wordAngle n i = Real.pi / 2) ∧
    (∀ i ∈ D.slotsAwayFrom a, ∃ q : ℕ, 3 ≤ q ∧
      Congruent (D.facet i) (duoprismModel n q) ∧
      D.wordAngle n i = Real.pi * (1 - 2 / (q : ℝ))) := by
  have hc := D.antiprism_count_le_one classification4D hP hG hn
  have huniq (i : Fin D.length) : Congruent (D.cell i) (antiprismModel n) ↔ i = a := by
    constructor
    · intro hi
      apply Finset.card_le_one.mp hc i _ a _
      · simp [antiprismRayIndices, hi]
      · simp [antiprismRayIndices, ha]
    · rintro rfl
      exact ha
  have hrot (i : Fin D.length) : D.cell (finRotate D.length i) = D.cell (i.val + 1) :=
    cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed i
  have hdis (i : ℕ) := unitUniform3_prism_antiprism_disjoint
    (polygonFace_unitPolygon hP hG).1 (D.cell_unitUniform hP hG i)
  refine ⟨huniq, ?_, ?_⟩
  · intro i hi
    have hend : i = a ∨ finRotate D.length i = a := by
      simpa only [D.slotsAwayFrom_mem, not_and_or, not_not] using hi
    rcases D.nonexceptional_slot classification4D hP hG hn i with
      ⟨q, hq, hK, hp, hp', hang⟩ | ⟨hK, _, hang⟩
    · rcases hend with hi | hi
      · exact (hdis i hp ((huniq i).mpr hi)).elim
      · have hh := (huniq (finRotate D.length i)).mpr hi
        rw [hrot] at hh
        exact (hdis (i.val + 1) hp' hh).elim
    · exact ⟨hK, hang⟩
  · intro i hi
    have hend := (D.slotsAwayFrom_mem a i).mp hi
    rcases D.nonexceptional_slot classification4D hP hG hn i with
      ⟨q, hq, hK, _, _, hang⟩ | ⟨hK, hpair, hang⟩
    · exact ⟨q, hq, hK, hang⟩
    · rcases hpair with ⟨ha', _⟩ | ⟨_, ha'⟩
      · exact (hend.1 ((huniq i).mp ha')).elim
      · rw [← hrot] at ha'
        exact (hend.2 ((huniq (finRotate D.length i)).mp ha')).elim

/-- The duoprism tail has less than pi available after the two right angles. -/
theorem antiprism_tail_budget (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (a : Fin D.length)
    (ha : Congruent (D.cell a) (antiprismModel n)) :
    (∑ i ∈ D.slotsAwayFrom a, D.wordAngle n i) < Real.pi := by
  have hp := (D.antiprism_slot_partition classification4D hP hG hn a ha).2.1
  have h0 : D.wordAngle n a = Real.pi / 2 := (hp a (by simp [slotsAwayFrom])).2
  have h1 : D.wordAngle n ((finRotate D.length).symm a) = Real.pi / 2 :=
    (hp _ (by simp [slotsAwayFrom])).2
  have he := Finset.sum_sdiff (f := fun i : Fin D.length => D.wordAngle n i)
    (show ({a, (finRotate D.length).symm a} : Finset (Fin D.length)) ⊆ Finset.univ from
      Finset.subset_univ _)
  change (∑ i ∈ D.slotsAwayFrom a, D.wordAngle n i) + _ = _ at he
  simp only [Finset.sum_pair (D.predecessor_ne a).symm, h0, h1] at he
  have hs : (∑ i : Fin D.length, D.wordAngle n i) < 2 * Real.pi := by
    rw [Fin.sum_univ_eq_sum_range]
    exact D.strict_perimeter hP hG
  linarith

end Uniform5.Composition.ActualPolygonCycle
