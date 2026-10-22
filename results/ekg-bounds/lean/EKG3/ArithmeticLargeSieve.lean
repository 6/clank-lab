import EKG3.SieveWeight
import Statement.TheoremT

namespace EKG3
open scoped BigOperators
open OAI.Ostmann

/-- Montgomery's arithmetic sieve for a finite set in N consecutive natural
integers. Residue zero is avoided at every prime at most Q. -/
theorem nat_interval_large_sieve (A : Finset ℕ) (J N Q : ℕ) (hQ : 1 ≤ Q)
    (hinterval : ∀ m ∈ A, J < m ∧ m ≤ J + N)
    (havoid : ∀ m ∈ A, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ m) :
    (A.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ)^2) / G Q := by
  classical
  have hG : 0 < G Q := (Real.log_nonneg (by exact_mod_cast hQ)).trans_lt (log_lt_G Q hQ)
  by_cases hA : A.Nonempty
  · have hN : 1 ≤ N := by
      obtain ⟨m, hm⟩ := hA
      obtain ⟨hlo, hhi⟩ := hinterval m hm
      omega
    let B := (Finset.univ : Finset (Fin N)).filter (fun n => J + 1 + n.val ∈ A)
    have hcard : B.card = A.card := by
      apply Finset.card_bij (fun n _ => J + 1 + n.val)
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · intro a _ b _ hab
        apply Fin.ext
        omega
      · intro m hm
        have hbounds := hinterval m hm
        refine ⟨⟨m - (J + 1), by omega⟩, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, by simpa only [Nat.add_sub_of_le (by omega : J+1 ≤ m)] using hm⟩
        · dsimp
          omega
    have hB : B.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Finset.card_pos.mpr hA)
    let S (p : ℕ) : Finset (ZMod p) :=
      if hp : p.Prime then
        letI : NeZero p := ⟨hp.ne_zero⟩
        Finset.univ.erase 0
      else ∅
    have hprime (p : ℕ) (hp : p ∈ sievePrimes Q) : p.Prime :=
      (Finset.mem_filter.mp hp).2
    have hS (p : ℕ) (hp : p ∈ sievePrimes Q) : (S p).Nonempty := by
      have hpp := hprime p hp
      let : Fact p.Prime := ⟨hpp⟩
      simp only [S, dite_eq_left hpp]
      exact ⟨1, by simp⟩
    have hScard (p : ℕ) (hp : p ∈ sievePrimes Q) : (S p).card = p - 1 := by
      have hpp := hprime p hp
      let : NeZero p := ⟨hpp.ne_zero⟩
      simp [S, hpp]
    have hres (x : Fin N) (hx : x ∈ B) (p : ℕ) (hp : p ∈ sievePrimes Q) :
        ((((J + 1 : ℕ) : ℤ) + (x.val : ℤ) : ℤ) : ZMod p) ∈ S p := by
      have hpp := hprime p hp
      let : NeZero p := ⟨hpp.ne_zero⟩
      have hm := (Finset.mem_filter.mp hx).2
      have hpQ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hd := havoid _ hm p hpp hpQ
      simp only [S, dite_eq_left hpp, Finset.mem_erase, Finset.mem_univ, and_true]
      have hz : ((J + 1 + x.val : ℕ) : ZMod p) ≠ 0 := by
        exact fun he => hd ((ZMod.natCast_eq_zero_iff _ _).mp he)
      simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one] using hz
    have h := prime_set_support_sieve (sievePrimes Q) hprime S hS hQ hN B hB
      ((J + 1 : ℕ) : ℤ) hres
    have hweight : (∑ U ∈ boundedSieveSubsets (sievePrimes Q) Q,
        ∏ p ∈ U, ((p : ℝ) / (S p).card - 1)) = G Q := by
      rw [← subset_weight_eq_G]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.prod_congr rfl
      intro p hp
      have hpP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp
      have hpp := hprime p hpP
      rw [hScard p hpP, Nat.cast_sub hpp.one_le, Nat.cast_one]
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      change (p : ℝ) / ((p : ℝ) - 1) - 1 = ((p : ℝ) - 1)⁻¹
      field_simp [ne_of_gt (sub_pos.mpr hpR)]
      ring
    rw [hweight, hcard] at h
    have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    apply (le_div_iff₀ hG).mpr
    simpa only [mul_comm] using (le_div_iff₀ hAc).mp h
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The arithmetic large sieve premise used by Theorem T is a theorem. -/
theorem arithmeticLargeSieve_holds : ArithmeticLargeSieve := by
  classical
  intro u Y N Q hQ hupper havoid
  have hQ1 : 1 ≤ Q := by omega
  have hinterval (m : ℕ) (hm : m ∈ roughSet EKG.canonical u Y) :
      EKG.frontier EKG.canonical u + Y < m ∧
      m ≤ EKG.frontier EKG.canonical u + Y + N :=
    ⟨(Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1, hupper m hm⟩
  have h := nat_interval_large_sieve (roughSet EKG.canonical u Y)
    (EKG.frontier EKG.canonical u + Y) N Q hQ1 hinterval havoid
  have hlog : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  exact h.trans (div_le_div_of_nonneg_left (by positivity) hlog (log_lt_G Q hQ1).le)

end EKG3
