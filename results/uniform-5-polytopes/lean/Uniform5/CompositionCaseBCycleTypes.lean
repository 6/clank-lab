import Uniform5.CompositionCaseBCycleRemainder

/-! F5 for actual polygon cycles, with concrete cell and facet families. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped BigOperators

/-- The exact unordered two-parameter list in F5(iii). -/
theorem typeIIIPair_of_angle_budget {q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r)
    (h : (1 - 2 / (q : ℝ)) + (1 - 2 / (r : ℝ)) < 1) :
    CaseB.TypeIIIPair q r := by
  have hone : q = 3 ∨ r = 3 := by
    by_contra hn
    have hq4 : 4 ≤ q := by omega
    have hr4 : 4 ≤ r := by omega
    have hq' := CaseB.polygon_angle_four_lower hq4
    have hr' := CaseB.polygon_angle_four_lower hr4
    linarith
  have hbound (t : ℕ) (ht : 3 ≤ t)
      (hh : (1 - 2 / (3 : ℝ)) + (1 - 2 / (t : ℝ)) < 1) :
      t ∈ ([3, 4, 5] : List ℕ) := by
    have ht5 : t ≤ 5 := by
      by_contra hgt
      have ht6 : (6 : ℝ) ≤ t := by exact_mod_cast (show 6 ≤ t by omega)
      have hd : (2 : ℝ) / t ≤ 2 / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht6
      linarith
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hone with rfl | rfl
  · exact Or.inl ⟨rfl, hbound r hr h⟩
  · exact Or.inr ⟨rfl, hbound q hq (by linarith)⟩

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- F5(i): every actual facet is a duoprism, and every actual cell a prism. -/
noncomputable def CaseBTypeI (n : ℕ) : Prop :=
  (D.length = 3 ∨ D.length = 4 ∨ D.length = 5) ∧
  ∃ q : Fin D.length → ℕ,
    (∀ i, 3 ≤ q i ∧ Congruent (D.facet i) (duoprismModel n (q i)) ∧
      Congruent (D.cell i) (polygonPrismModel n)) ∧
    (∑ i, (1 - 2 / (q i : ℝ))) < 2

/-- F5(ii): the two facets at the antiprism ray and one remaining duoprism. -/
noncomputable def CaseBTypeII (n : ℕ) : Prop :=
  D.length = 3 ∧ ∃ a i : Fin D.length, ∃ q : ℕ, 3 ≤ q ∧
    Congruent (D.cell a) (antiprismModel n) ∧ D.slotsAwayFrom a = {i} ∧
    (∀ j, j ≠ a → Congruent (D.cell j) (polygonPrismModel n)) ∧
    (∀ j, j ∉ D.slotsAwayFrom a → Congruent (D.facet j) (antiprismPrismModel n)) ∧
    Congruent (D.facet i) (duoprismModel n q)

/-- F5(iii): the same two adjacent antiprism-prisms and exactly the stated
unordered pair of duoprism parameters. -/
noncomputable def CaseBTypeIII (n : ℕ) : Prop :=
  D.length = 4 ∧ ∃ a i j : Fin D.length, ∃ q r : ℕ,
    i ≠ j ∧ 3 ≤ q ∧ 3 ≤ r ∧ CaseB.TypeIIIPair q r ∧
    Congruent (D.cell a) (antiprismModel n) ∧ D.slotsAwayFrom a = {i, j} ∧
    (∀ t, t ≠ a → Congruent (D.cell t) (polygonPrismModel n)) ∧
    (∀ t, t ∉ D.slotsAwayFrom a → Congruent (D.facet t) (antiprismPrismModel n)) ∧
    Congruent (D.facet i) (duoprismModel n q) ∧ Congruent (D.facet j) (duoprismModel n r)

theorem cell_prism_of_not_antiprism (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (i : Fin D.length)
    (hi : ¬ Congruent (D.cell i) (antiprismModel n)) :
    Congruent (D.cell i) (polygonPrismModel n) := by
  rcases D.nonexceptional_slot classification4D hP hG hn i with
    ⟨_, _, _, hp, _, _⟩ | ⟨_, hpair, _⟩
  · exact hp
  · rcases hpair with ⟨ha, _⟩ | ⟨hp, _⟩
    · exact (hi ha).elim
    · exact hp

/-- F5 is derived from actual incidence, strict convexity, and the cited
four-dimensional family classification; no cycle-type premise is supplied. -/
theorem nonexceptional_cycle_types (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) :
    D.CaseBTypeI n ∨ D.CaseBTypeII n ∨ D.CaseBTypeIII n := by
  by_cases hex : ∃ a : Fin D.length, Congruent (D.cell a) (antiprismModel n)
  · obtain ⟨a, ha⟩ := hex
    obtain ⟨huniq, hright, htail⟩ :=
      D.antiprism_slot_partition classification4D hP hG hn a ha
    have hother (j : Fin D.length) (hj : j ≠ a) :
        Congruent (D.cell j) (polygonPrismModel n) :=
      D.cell_prism_of_not_antiprism classification4D hP hG hn j (fun h => hj ((huniq j).mp h))
    have hright' (j : Fin D.length) (hj : j ∉ D.slotsAwayFrom a) := (hright j hj).1
    rcases D.antiprism_length_cases classification4D hP hG hn ⟨a, ha⟩ with hlen | hlen
    · have hc : (D.slotsAwayFrom a).card = 1 := by rw [D.slotsAwayFrom_card, hlen]
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      obtain ⟨q, hq, hK, _⟩ := htail i (by rw [hi]; simp)
      exact Or.inr (Or.inl ⟨hlen, a, i, q, hq, ha, hi, hother, hright', hK⟩)
    · have hc : (D.slotsAwayFrom a).card = 2 := by rw [D.slotsAwayFrom_card, hlen]
      obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hc
      obtain ⟨q, hq, hK, hangle⟩ := htail i (by rw [he]; simp)
      obtain ⟨r, hr, hL, hangle'⟩ := htail j (by rw [he]; simp)
      have hb := D.antiprism_tail_budget classification4D hP hG hn a ha
      rw [he, Finset.sum_pair hij, hangle, hangle'] at hb
      have hbudget : (1 - 2 / (q : ℝ)) + (1 - 2 / (r : ℝ)) < 1 := by
        nlinarith [Real.pi_pos]
      exact Or.inr (Or.inr ⟨hlen, a, i, j, q, r, hij, hq, hr,
        typeIIIPair_of_angle_budget hq hr hbudget, ha, he, hother, hright', hK, hL⟩)
  · have hnone (i : Fin D.length) : ¬ Congruent (D.cell i) (antiprismModel n) :=
      fun hi => hex ⟨i, hi⟩
    have hchoice (i : Fin D.length) : ∃ q : ℕ, 3 ≤ q ∧
        Congruent (D.facet i) (duoprismModel n q) ∧
        D.wordAngle n i = Real.pi * (1 - 2 / (q : ℝ)) := by
      rcases D.nonexceptional_slot classification4D hP hG hn i with
        ⟨q, hq, hK, _, _, ha⟩ | ⟨_, hpair, _⟩
      · exact ⟨q, hq, hK, ha⟩
      · rcases hpair with ⟨ha, _⟩ | ⟨_, ha⟩
        · exact (hnone i ha).elim
        · have hrot := cycle_apply_finRotate (by have := D.length_ge; omega)
            D.cell D.cell_closed i
          rw [← hrot] at ha
          exact (hnone (finRotate D.length i) ha).elim
    choose q hq using hchoice
    have hlen := D.nonexceptional_length_le_five classification4D hP hG hn
    refine Or.inl ⟨by have := D.length_ge; omega, q, ?_, ?_⟩
    · intro i
      exact ⟨(hq i).1, (hq i).2.1,
        D.cell_prism_of_not_antiprism classification4D hP hG hn i (hnone i)⟩
    · have hs : (∑ i : Fin D.length, D.wordAngle n i) < 2 * Real.pi := by
        rw [Fin.sum_univ_eq_sum_range]
        exact D.strict_perimeter hP hG
      have he : (∑ i : Fin D.length, D.wordAngle n i) =
          Real.pi * ∑ i, (1 - 2 / (q i : ℝ)) := by
        simp_rw [(hq _).2.2]
        rw [Finset.mul_sum]
      rw [he] at hs
      nlinarith [Real.pi_pos]

end ActualPolygonCycle
end Uniform5.Composition
