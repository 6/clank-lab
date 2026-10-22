import Statement.LemmaD
import EKG.PrimeStructureGlobal
import EKG.CrossingBounds

namespace EKG3
open EKG

private theorem peak_ge (s : GreedySeq) (u : ℕ) :
    earlyEvenCount s u ≤ priorPeak s u :=
  Finset.le_sup (Finset.mem_range.mpr (by omega))

/-- All structural conclusions for one predecessor. The span theorem at
state `u` excludes tick predecessors directly, so no small-index L6 input
or historical-index lower bound is needed. -/
private theorem predecessor (s : GreedySeq) (u Y i : ℕ)
    (hY : 6 * priorPeak s u + 7 ≤ Y)
    (hi : i ∈ oddExcess s u Y) :
    2 ≤ i ∧ i ≤ u ∧ 1 < s.a (i-1) ∧ ¬ (s.a (i-1)).Prime ∧
      ¬ spanTickValue (s.a (i-1)) ∧ s.a (i-1) ≤ nonTickTop s u ∧
      (∀ r : ℕ, r.Prime → r ∣ s.a (i-1) →
        Y+1 ≤ 2*(earlyEvenCount s u+1)*r) := by
  classical
  obtain ⟨hir, hodd, hlarge, hnot⟩ := Finset.mem_filter.mp hi
  have hit : i ≤ u := by have := Finset.mem_range.mp hir; omega
  have hin : 2 ≤ i := by
    by_contra h
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with hc | hc
    · rw [hc, s.seed_zero] at hlarge; omega
    · rw [hc, s.seed_one] at hlarge; omega
  have hprev : i-1+1 = i := by omega
  have hprevobs : i-1 ≤ u := by omega
  have htwo : ¬ 2 ∣ s.a (i-1) := by
    intro hd
    have hsmall := next_after_even_le_frontier s hd
    rw [hprev] at hsmall
    have := frontier_monotone s hprevobs
    omega
  have hone : s.a (i-1) ≠ 1 := by
    intro hv
    have := s.injective (hv.trans s.seed_zero.symm)
    omega
  have hcomp : ¬ (s.a (i-1)).Prime := by
    intro hp
    have hp2 : s.a (i-1) ≠ 2 := by
      intro hv; apply htwo; rw [hv]
    have hb := prime_occurrence_block s hp hp2 rfl
    apply hnot
    refine ⟨s.a (i-1), hp, hp2, ?_⟩
    simpa only [hprev] using hb.2.2.1
  have hrough : ∀ r : ℕ, r.Prime → r ∣ s.a (i-1) →
      Y+1 ≤ 2*(earlyEvenCount s u+1)*r := by
    intro r hr hrd
    have hb := s.term_le_frontier_add hin (by omega : i ≤ u+1) hr hrd
    nlinarith
  have hnt : ¬ spanTickValue (s.a (i-1)) := by
    rintro ⟨p, hp, hp2, hv⟩
    have hd : 3 ∣ s.a (i-1) := by rw [hv]; exact Nat.dvd_mul_right 3 p
    have hb := hrough 3 Nat.prime_three hd
    have hk := peak_ge s u
    omega
  exact ⟨hin, hit, by have := s.positive (i-1); omega,
    hcomp, hnt, nonTick_le_top s hprevobs hnt, hrough⟩

theorem lemmaD : LemmaDStatement := by
  classical
  intro s u Y hY
  let S := oddExcess s u Y
  let X := frontier s u + Y + 1
  let A := S.filter (fun i => s.a (i-1) < X)
  let B := S.filter (fun i => ¬ s.a (i-1) < X)
  let U := A.image (fun i => i-1)
  have hdata (i : ℕ) (hi : i ∈ S) := predecessor s u Y i hY hi
  have hU : U.card ≤ Nat.primeCounting (Nat.sqrt X) := by
    apply s.composite_upcrossings_bound
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have hd := hdata i (Finset.mem_filter.mp hi).1
      exact ⟨hd.2.2.1, hd.2.2.2.1⟩
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hiS, hilow⟩ := Finset.mem_filter.mp hi
      have hd := hdata i hiS
      have hprev : i-1+1 = i := by omega
      refine ⟨hilow, ?_⟩
      rw [hprev]
      have := (Finset.mem_filter.mp hiS).2.2.1
      dsimp [X]
      omega
  have hA : A.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (fun i => i-1)
    · intro i hi; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · intro i hi j hj hij
      change i-1 = j-1 at hij
      have hi2 := (hdata i (Finset.mem_filter.mp hi).1).1
      have hj2 := (hdata j (Finset.mem_filter.mp hj).1).1
      omega
  have hB : B.card ≤ (roughSet s u Y).card := by
    apply Finset.card_le_card_of_injOn (fun i => s.a (i-1))
    · intro i hi
      obtain ⟨hiS, hhigh⟩ := Finset.mem_filter.mp hi
      have hd := hdata i hiS
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, hd.2.2.2.2.2.1⟩, hd.2.2.2.2.2.2⟩
      dsimp [X] at hhigh
      change frontier s u + Y < s.a (i-1)
      omega
    · intro i hi j hj hij
      have heq := s.injective hij
      have hi2 := (hdata i (Finset.mem_filter.mp hi).1).1
      have hj2 := (hdata j (Finset.mem_filter.mp hj).1).1
      omega
  have hcover : S ⊆ A ∪ B := by
    intro i hi
    by_cases h : s.a (i-1) < X
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h⟩)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le A B)
  exact hc.trans (Nat.add_le_add (hA.trans hU) hB)

end EKG3
