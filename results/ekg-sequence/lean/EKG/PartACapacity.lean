import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
Fixed-modulus prime capacity, uniformly in the position of a real interval.
No asymptotic prime-counting theorem is used: divergence of prime reciprocals
chooses one modulus, after which elementary periodic coprime counting suffices.
-/

namespace EKG.PartA

open Finset

private lemma prod_one_sub_mul_one_add_sum_le_one
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    (∏ i ∈ S, (1 - x i)) * (1 + ∑ i ∈ S, x i) ≤ 1 := by
  classical
  revert hx
  induction S using Finset.induction_on with
  | empty => intro hx; simp
  | @insert i S hi ih =>
    intro hx
    have hxi := hx i (mem_insert_self i S)
    have hxS : ∀ j ∈ S, 0 ≤ x j ∧ x j ≤ 1 :=
      fun j hj => hx j (mem_insert_of_mem hj)
    have hP : 0 ≤ ∏ j ∈ S, (1 - x j) :=
      prod_nonneg fun j hj => sub_nonneg.mpr (hxS j hj).2
    have hQ : 0 ≤ ∑ j ∈ S, x j :=
      sum_nonneg fun j hj => (hxS j hj).1
    have hPQ := ih hxS
    rw [prod_insert hi, sum_insert hi]
    have herror := mul_nonneg (mul_nonneg hP hxi.1) (add_nonneg hQ hxi.1)
    nlinarith

/-- A finite collection of primes whose reciprocal sum exceeds any given bound. -/
private lemma exists_prime_finset_large_reciprocal_sum (B : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ B < ∑ p ∈ S, (1 : ℝ) / p := by
  classical
  by_contra h
  push_neg at h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := B)
  · intro n
    exact Set.indicator_nonneg (fun _ _ => by positivity) n
  · intro F
    simpa only [Finset.sum_filter, Set.indicator_apply, Set.mem_setOf_eq] using
      h (F.filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2)

/-- The modulus is selected once, as a function of `eta` alone. -/
theorem exists_modulus_totient_density (eta : ℝ) (heta : 0 < eta) :
    ∃ W : ℕ, W ≠ 0 ∧ (W.totient : ℝ) / W < eta := by
  classical
  obtain ⟨S, hS, hsum⟩ := exists_prime_finset_large_reciprocal_sum (1 / eta)
  let W : ℕ := ∏ p ∈ S, p
  have hW : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW
  have hfac : W.primeFactors = S := Nat.primeFactors_prod hS
  have hphi : (W.totient : ℝ) = (W : ℝ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    rw [← hfac]
    have h := congrArg (fun q : ℚ => (q : ℝ))
      (Nat.totient_eq_mul_prod_factors W)
    push_cast at h
    exact h
  have hrho : (W.totient : ℝ) / W = ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    apply (div_eq_iff hWr).mpr
    simpa only [mul_comm] using hphi
  have hx : ∀ p ∈ S, 0 ≤ (1 : ℝ) / p ∧ (1 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_le
    exact ⟨by positivity, (div_le_one (by positivity)).mpr hp1⟩
  have hprod := prod_one_sub_mul_one_add_sum_le_one S (fun p => (1 : ℝ) / p) hx
  simp only [one_div] at hprod
  rw [← hrho] at hprod
  have hlarge : 1 < (∑ p ∈ S, (1 : ℝ) / p) * eta :=
    (div_lt_iff₀ heta).mp hsum
  have hs0 : 0 ≤ ∑ p ∈ S, (1 : ℝ) / p := sum_nonneg fun p hp => (hx p hp).1
  have hr0 : 0 ≤ (W.totient : ℝ) / W := by positivity
  refine ⟨W, hW, ?_⟩
  by_contra hbad
  have hbad' : eta ≤ (W.totient : ℝ) / W := le_of_not_gt hbad
  have hmul := mul_nonneg (sub_nonneg.mpr hbad') hs0
  simp only [one_div] at hlarge hs0 hmul
  nlinarith

/-- All primes in a natural interval consist of coprime residues and at most
the prime divisors of the fixed modulus. The right endpoint is exclusive. -/
theorem prime_finset_card_le_modulus_interval
    (W : ℕ) (hW : W ≠ 0) (F : Finset ℕ) (m L : ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ m ≤ p ∧ p < m + L) :
    F.card ≤ W.totient * (L / W + 1) + W.primeFactors.card := by
  classical
  let A := (Finset.Ico m (m + L)).filter (Nat.Coprime W)
  have hsub : F ⊆ A ∪ W.primeFactors := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := hF p hp
    by_cases hc : W.Coprime p
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨hlo, hhi⟩, hc⟩)
    · apply mem_union_right
      apply hpp.mem_primeFactors _ hW
      apply hpp.dvd_iff_not_coprime.mpr
      simpa only [Nat.coprime_comm] using hc
  calc
    F.card ≤ (A ∪ W.primeFactors).card := card_le_card hsub
    _ ≤ A.card + W.primeFactors.card := card_union_le _ _
    _ ≤ W.totient * (L / W + 1) + W.primeFactors.card :=
      Nat.add_le_add_right (Nat.Ico_filter_coprime_le m L hW) _

/-- Prime capacity in every real window, with an arbitrarily small linear
coefficient. `C` and the fixed modulus depend only on `eta`, never on `a`,
`z`, or the finite collection of primes. -/
theorem prime_capacity_real_windows (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset ℕ) (a z : ℝ), 0 ≤ z →
      (∀ p ∈ F, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a + z) →
      (F.card : ℝ) ≤ eta * z + C := by
  classical
  obtain ⟨W, hW, hdensity⟩ := exists_modulus_totient_density eta heta
  let C : ℝ := eta + (W.totient : ℝ) + (W.primeFactors.card : ℝ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro F a z hz hF
  by_cases hne : F.Nonempty
  · let m := F.min' hne
    let n := F.max' hne
    have hm : m ∈ F := min'_mem F hne
    have hn : n ∈ F := max'_mem F hne
    have hmn : m ≤ n := min'_le_max' F hne
    let L := n - m + 1
    have hinterval : ∀ p ∈ F, p.Prime ∧ m ≤ p ∧ p < m + L := by
      intro p hp
      refine ⟨(hF p hp).1, min'_le F p hp, ?_⟩
      have hpmax : p ≤ n := le_max' F p hp
      dsimp [L]
      omega
    have hcount := prime_finset_card_le_modulus_interval W hW F m L hinterval
    have hcast : (F.card : ℝ) ≤
        (W.totient : ℝ) * (((L / W : ℕ) : ℝ) + 1) + W.primeFactors.card := by
      exact_mod_cast hcount
    have hdiv : ((L / W : ℕ) : ℝ) ≤ (L : ℝ) / W := Nat.cast_div_le
    have hmul := mul_le_mul_of_nonneg_left hdiv
      (show (0 : ℝ) ≤ W.totient by positivity)
    have hlen : (L : ℝ) ≤ z + 1 := by
      have hreal := (hF n hn).2.2
      have hreal' := (hF m hm).2.1
      dsimp [L]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hmn]
      linarith
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hdL := mul_le_mul_of_nonneg_right (le_of_lt hdensity) hL0
    have hlen' := mul_le_mul_of_nonneg_left hlen (le_of_lt heta)
    have hidentity : (W.totient : ℝ) * ((L : ℝ) / W) =
        ((W.totient : ℝ) / W) * L := by ring
    dsimp [C]
    nlinarith
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    simp only [card_empty, Nat.cast_zero]
    exact add_nonneg (mul_nonneg (le_of_lt heta) hz) (by dsimp [C]; positivity)

end EKG.PartA
