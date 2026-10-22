import EKG3.ArithmeticLargeSieve
import EKG3.SieveFromEnergy
import EKG.PrimeStructureLarge

namespace EKG3
open scoped BigOperators
open OAI.Ostmann

theorem nat_interval_large_sieve_refined (A : Finset ℕ) (J N Q : ℕ) (hQ : 2 ≤ Q)
    (hinterval : ∀ m ∈ A, J < m ∧ m ≤ J + N)
    (havoid : ∀ m ∈ A, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ m) :
    (A.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ)^2 - 1) / G Q := by
  classical
  have hQ1 : 1 ≤ Q := by omega
  have hG : 0 < G Q := (Real.log_nonneg (by exact_mod_cast hQ1)).trans_lt (log_lt_G Q hQ1)
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
    have h := prime_set_support_sieve_from_energy (sievePrimes Q) hprime S hS hQ1 hN B hB
      ((J + 1 : ℕ) : ℤ) hres
      (additiveSieve_probability_bound_refined hQ B hB ((J + 1 : ℕ) : ℤ))
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
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply div_nonneg _ hG.le
    have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith

/-- Large-sieve Brun–Titchmarsh bound, using exactly the realPrimeCount
floor convention of Theorem T. This is distinct from its strict BT input. -/
theorem largeSieveBT (x y : ℝ) (Q : ℕ) (hx : 0 < x) (hy : 1 ≤ y) (hQ : 1 ≤ Q) :
    EKG.realPrimeCount (x+y) - EKG.realPrimeCount x ≤
      (y + (Q : ℝ)^2) / G Q + EKG.realPrimeCount Q := by
  classical
  let J := ⌊x⌋₊
  let R := ⌊x+y⌋₊
  let N := R - J
  let P := (Finset.Ioc J R).filter Nat.Prime
  have hJR : J ≤ R := Nat.floor_mono (by linarith : x ≤ x+y)
  have hN : (N : ℝ) < y+1 := by
    have hr : (R : ℝ) ≤ x+y := Nat.floor_le (by linarith)
    have hj : x < (J : ℝ)+1 := Nat.lt_floor_add_one x
    dsimp [N]
    rw [Nat.cast_sub hJR]
    linarith
  have hpi : EKG.realPrimeCount (x+y) - EKG.realPrimeCount x = (P.card : ℝ) := by
    have hc := EKG.primeStructure_prime_Ioc_card J R hJR
    rw [hc, Nat.cast_sub (Nat.monotone_primeCounting hJR)]
    rfl
  rw [hpi]
  by_cases hQ2 : 2 ≤ Q
  · let A := P.filter (fun m => Q < m)
    have hinterval (m : ℕ) (hm : m ∈ A) : J < m ∧ m ≤ J+N := by
      have hmP := (Finset.mem_filter.mp hm).1
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hmP).1
      exact ⟨hlo, by dsimp [N]; omega⟩
    have havoid (m : ℕ) (hm : m ∈ A) (p : ℕ) (hp : p.Prime) (hpQ : p ≤ Q) : ¬ p ∣ m := by
      have hmpr := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      have hmQ := (Finset.mem_filter.mp hm).2
      intro hd
      rcases (Nat.dvd_prime hmpr).mp hd with h1 | hpm
      · exact hp.ne_one h1
      · omega
    have hA := nat_interval_large_sieve_refined A J N Q hQ2 hinterval havoid
    have hG : 0 < G Q := (Real.log_nonneg (by exact_mod_cast hQ)).trans_lt (log_lt_G Q hQ)
    have hnum : ((N : ℝ) + (Q : ℝ)^2 - 1) / G Q ≤ (y + (Q : ℝ)^2) / G Q :=
      div_le_div_of_nonneg_right (by linarith) hG.le
    have hcount : P.card ≤ A.card + Nat.primeCounting Q := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun m => Q < m)
      have hsmall : (P.filter (fun m => ¬ Q < m)).card ≤ Nat.primeCounting Q := by
        rw [← Nat.primesLE_card_eq_primeCounting]
        apply Finset.card_le_card
        intro m hm
        obtain ⟨hmP, hmQ⟩ := Finset.mem_filter.mp hm
        exact Nat.mem_primesLE.mpr ⟨by omega, (Finset.mem_filter.mp hmP).2⟩
      dsimp [A]
      omega
    have hcountR : (P.card : ℝ) ≤ (A.card : ℝ) + Nat.primeCounting Q := by exact_mod_cast hcount
    have hpiQ : EKG.realPrimeCount Q = (Nat.primeCounting Q : ℝ) := by
      simp only [EKG.realPrimeCount, Nat.floor_natCast]
    rw [hpiQ]
    linarith [hA.trans hnum]
  · have hQeq : Q = 1 := by omega
    subst Q
    have hG1 : G 1 = 1 := by
      simp only [G, Finset.Icc_self, Finset.sum_filter, Finset.sum_singleton]
      rw [ite_eq_left (squarefree_one : Squarefree (1 : ℕ))]
      norm_num
    have hcardN : P.card ≤ N := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp [N])
    have hcardR : (P.card : ℝ) ≤ N := by exact_mod_cast hcardN
    norm_num [hG1, EKG.realPrimeCount]
    linarith

end EKG3
