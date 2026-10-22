import Statement.LemmaA
import EKG.PrimeStructureGlobal
import EKG.FiniteBase

namespace EKG3
open EKG

/-- Strengthened local window. Interior ticks transfer the unused
3-frontier back across the block, then count at the pre-block state.
The possible final tick uses the elementary frontier advance instead. -/
theorem lemmaA : LemmaAStatement := by
  classical
  intro s u i hu
  obtain ⟨hup, hnot⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hir, hp, hlow, hhigh⟩ := Finset.mem_filter.mp hup
  have hiu : i < u := Finset.mem_range.mp hir
  have hp2 : s.a i ≠ 2 := by
    intro heq
    have hi1 : i = 1 := s.injective (heq.trans s.seed_one.symm)
    have hfour : s.a (i+1) = 4 := by
      rw [hi1]; exact FiniteBase.first_thirteen s (by omega)
    have hmono := frontier_monotone s (show 2 ≤ u by omega)
    rw [FiniteBase.frontier_eq s (by omega : 2 < 13)] at hmono
    norm_num [FiniteBase.frontierValue] at hmono
    omega
  obtain ⟨hi, htwo, htick, hbefore⟩ := prime_occurrence_block s hp hp2 rfl
  have hodd := primeStructure_odd_not_two_dvd hp hp2
  have htodd := primeStructure_tick_not_two_dvd hp hp2
  have hk : earlyEvenCount s (i-2) ≤ EKG.priorPeak (earlyEvenCount s) u :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hle : 2*s.a i ≤ frontier s u := by
    rw [← hbefore]; exact frontier_monotone s (by omega)
  have hne : 2*s.a i ≠ frontier s u := by
    intro he; exact frontier_ne_used s (by omega : i-1 ≤ u) (htwo.trans he)
  refine ⟨hp, by omega, ?_⟩
  have hetick : frontier s u < 3*s.a i := by
    have hne := frontier_ne_used s (show i+1 ≤ u by omega)
    rw [htick] at hne
    omega
  by_cases hit : i+1 < u
  · by_cases hp3 : s.a i = 3
    · omega
    have hB : frontier s u < multiple3Frontier s (i+1) := by
      by_contra h
      exact hnot (tick_self_paired s hup hit htick htodd (by omega))
    have hBbefore : frontier s u < multiple3Frontier s (i-2) := by
      by_contra h
      let b := multiple3Frontier s (i-2)
      have hb := multiple3Frontier_spec s (i-2)
      have hbpos : 0 < b := hb.1
      have hb3 : 3 ∣ b := hb.2.1
      have hbe : b ≤ frontier s u := by dsimp [b]; omega
      obtain ⟨j, hj, hjb⟩ := smaller_multiple3_used s hbpos hb3
        (show b < multiple3Frontier s (i+1) by omega)
      have hjlow : i-2 < j := by
        by_contra hjlo
        exact hb.2.2 ⟨j, by omega, hjb⟩
      have hjcases : j = i-1 ∨ j = i ∨ j = i+1 := by omega
      have h3p : ¬ 3 ∣ s.a i := by
        intro hd
        exact hp3 ((hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd)
      rcases hjcases with rfl | rfl | rfl
      · rw [htwo] at hjb
        have hd : 3 ∣ 2*s.a i := hjb.symm ▸ hb3
        exact (Nat.prime_three.not_dvd_mul (by decide : ¬ 3 ∣ 2) h3p) hd
      · exact h3p (hjb.symm ▸ hb3)
      · rw [htick] at hjb; omega
    have hc := multiple6_interval_card_le_earlyEvenCount s (i-2)
    rw [hbefore, Nat.card_Ico] at hc
    have hbdiv := (multiple3Frontier_spec s (i-2)).2.1
    obtain ⟨q, hq⟩ := hbdiv
    omega
  · have hfinal : u = i+1 := by omega
    have hadvance := frontier_advance_tick_block s (k := i+1) (by omega)
      (show s.a (i+1-2) = 2*s.a i by simpa only [show i+1-2 = i-1 by omega] using htwo)
      (show ¬ 2 ∣ s.a (i+1-1) by simpa only [show i+1-1 = i by omega] using hodd)
      (show ¬ 2 ∣ s.a (i+1) by rwa [htick])
      (show frontier s (i+1-3) = 2*s.a i by simpa only [show i+1-3 = i-2 by omega] using hbefore)
    have hsub : i+1-3 = i-2 := by omega
    rw [hsub] at hadvance
    have hb : frontier s u ≤ 2*s.a i + 2*earlyEvenCount s (i-2) + 2 := by
      rw [hfinal]; exact hadvance
    omega

end EKG3
