import Statement.LemmaC

namespace EKG3
open EKG

/-- The only bootstrap call is at `b`, just before first passage.
In particular `b < u`; no bound at the current state is used. -/
theorem lemmaC1 : LemmaC1Statement := by
  intro s u M hM hlocal h hh hnp hbelow hfree
  obtain ⟨b, hbu, hearlier, hstart⟩ := MissingComposites.first_passage s hh hbelow
  have hK : earlyEvenCount s b ≤ M h :=
    (hlocal b (by omega)).trans (hM hearlier)
  exact MissingComposites.hole_span s (primeIntroductionPattern s)
    hh hnp hbelow hfree hbu hearlier hstart hK

/-- The small states have no holes, by the archive's certified prefix.
This removes even the archive counting theorem's `8 ≤ u` restriction. -/
private theorem holesBelow_card_zero (s : GreedySeq) {u : ℕ} (hu : u < 8) :
    (HoleCounting.holesBelow s u).card = 0 := by
  classical
  have he : HoleCounting.holesBelow s u =
      ((Finset.Ico 1 (FiniteBase.frontierValue u)).filter
        (fun h => ¬ h.Prime ∧ h ∉ FiniteBase.usedSet u)) := by
    ext h
    simp only [HoleCounting.holesBelow, Finset.mem_filter,
      FiniteBase.frontier_eq s (by omega : u < 13),
      FiniteBase.usedBefore_iff_mem s (by omega : u < 13)]
  rw [he]
  exact (by decide : ∀ v : Fin 8,
    ((Finset.Ico 1 (FiniteBase.frontierValue v.val)).filter
      (fun h => ¬ h.Prime ∧ h ∉ FiniteBase.usedSet v.val)).card = 0) ⟨u, hu⟩

theorem lemmaC2 : LemmaC2Statement := by
  intro s u M hM hlocal
  rw [← HoleCounting.holesBelow_eq_clock_holes]
  by_cases hu : u < 8
  · rw [holesBelow_card_zero s hu]
    exact Nat.zero_le _
  · have hcount := HoleCounting.card_le_primeCounting_mul
      (HoleCounting.holesBelow s u)
      (e := frontier s u)
      (M := Nat.primeCounting (Nat.sqrt (frontier s u)) + M (frontier s u) + 4)
    apply hcount
    intro h hh
    have hs := HoleCounting.holesBelow_spec s hh
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    have h15 := HoleCounting.missing_composite_ge_fifteen s (by omega)
      hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2
    have hspan := lemmaC1 s u M hM hlocal h h15 hs.2.1 hs.2.2.2.1 hs.2.2.2.2
    have hp := Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hs.2.2.2.1.le)
    have hm := hM hs.2.2.2.1.le
    exact hspan.trans (Nat.mul_le_mul_left (2*h.minFac) (by omega))

theorem lemmaC : LemmaCStatement := ⟨lemmaC1, lemmaC2⟩

end EKG3
