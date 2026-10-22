import EKG3.SieveWeightLog

/-! An elementary lower envelope for G: retain the exact local factors at
2 and 3, and use harmonic weights at the remaining primes. -/
namespace EKG3
open scoped BigOperators
open OAI.Ostmann

noncomputable def sieveSum (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ U ∈ boundedSieveSubsets P X, sieveWeight U

lemma sieveSum_insert (P : Finset ℕ) (p X : ℕ) (hp : 0 < p) (hpP : p ∉ P) :
    sieveSum (insert p P) X = sieveSum P X + ((p : ℝ)-1)⁻¹ * sieveSum P (X/p) := by
  classical
  simp only [sieveSum, boundedSieveSubsets, Finset.sum_filter]
  rw [Finset.sum_powerset_insert hpP]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hpU : p ∉ U := fun h => hpP (Finset.mem_powerset.mp hU h)
  rw [Finset.prod_insert hpU]
  have hle : p * (∏ q ∈ U, q) ≤ X ↔ (∏ q ∈ U, q) ≤ X/p := by
    rw [Nat.le_div_iff_mul_le hp, mul_comm]
  simp only [hle]
  by_cases hprod : (∏ q ∈ U, q) ≤ X/p
  · simp only [hprod, ite_true, sieveWeight, Finset.prod_insert hpU]
  · simp only [hprod, ite_false, mul_zero]

noncomputable def coprimeSixHarmonic (X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (n : ℝ)⁻¹

lemma coprimeSixHarmonic_le_sieveSum (P : Finset ℕ) (X : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ n ∈ Finset.Icc 1 X, ¬ 2 ∣ n → ¬ 3 ∣ n → n.primeFactors ⊆ P) :
    coprimeSixHarmonic X ≤ sieveSum P X := by
  classical
  let F := (Finset.Icc 1 X).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n)
  have hmap (n : ℕ) (hn : n ∈ F) : n.primeFactors ∈ boundedSieveSubsets P X := by
    obtain ⟨hnI, h2, h3⟩ := Finset.mem_filter.mp hn
    have hn1 := (Finset.mem_Icc.mp hnI).1
    have hnX := (Finset.mem_Icc.mp hnI).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (hcover n hnI h2 h3),
      (Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)).trans hnX⟩
  change (∑ n ∈ F, (n : ℝ)⁻¹) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun n : ℕ => (n : ℝ)⁻¹)]
  apply Finset.sum_le_sum
  intro U hU
  have hUpr : ∀ p ∈ U, p.Prime := fun p hp =>
    hP p (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp)
  apply le_trans _ (reciprocal_primeFactors_fiber_le U hUpr X)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
  · intro n _ _
    positivity

noncomputable def twoThreeEnvelope (Q : ℕ) : ℝ :=
  coprimeSixHarmonic Q + coprimeSixHarmonic (Q/2) +
    (1/2)*coprimeSixHarmonic (Q/3) + (1/2)*coprimeSixHarmonic (Q/6)

lemma twoThreeEnvelope_le_G (Q : ℕ) (hQ : 3 ≤ Q) : twoThreeEnvelope Q ≤ G Q := by
  classical
  let P := (sievePrimes Q).erase 2 |>.erase 3
  have h2P : 2 ∉ P := by simp [P]
  have h3P : 3 ∉ P := by simp [P]
  have hP : ∀ p ∈ P, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))).2
  have hcover (X : ℕ) (hX : X ≤ Q) :
      coprimeSixHarmonic X ≤ sieveSum P X := by
    apply coprimeSixHarmonic_le_sieveSum P X hP
    intro n hn h2 h3 p hp
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    have hp2 : p ≠ 2 := by rintro rfl; exact h2 hpn
    have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpn
    have hpQ : p ≤ Q := (Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 hpn).trans
      ((Finset.mem_Icc.mp hn).2.trans hX)
    exact Finset.mem_erase.mpr ⟨hp3, Finset.mem_erase.mpr ⟨hp2,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, hpQ⟩, hpp⟩⟩⟩
  have hrestore : insert 2 (insert 3 P) = sievePrimes Q := by
    have h2 : 2 ∈ sievePrimes Q :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by norm_num⟩
    have h3 : 3 ∈ sievePrimes Q :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hQ⟩, by norm_num⟩
    ext p
    simp only [Finset.mem_insert, P, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨_, _, hp⟩) <;> assumption
    · intro hp
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · by_cases hp3 : p = 3
        · exact Or.inr (Or.inl hp3)
        · exact Or.inr (Or.inr ⟨hp3, hp2, hp⟩)
  have h2P3 : 2 ∉ insert 3 P := by simp [h2P]
  rw [← subset_weight_eq_G]
  change twoThreeEnvelope Q ≤ sieveSum (sievePrimes Q) Q
  rw [← hrestore, sieveSum_insert _ 2 Q (by omega) h2P3,
    sieveSum_insert P 3 Q (by omega) h3P,
    sieveSum_insert P 3 (Q/2) (by omega) h3P]
  have hdiv : Q / 2 / 3 = Q / 6 := by rw [Nat.div_div_eq_div_mul]
  norm_num only [Nat.cast_ofNat, sub_self, inv_one, sub_zero] at *
  norm_num at hdiv ⊢
  dsimp [twoThreeEnvelope]
  have h1 := hcover Q le_rfl
  have h2 := hcover (Q/2) (Nat.div_le_self Q 2)
  have h3 := hcover (Q/3) (Nat.div_le_self Q 3)
  have h6 := hcover (Q/6) (Nat.div_le_self Q 6)
  rw [hdiv]
  linarith

lemma harmonic_multiples_sum (Q d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => d ∣ n), (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * (harmonic (Q/d) : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun k _ => d*k)
  · intro k hk
    obtain ⟨hk1, hkQ⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right d k⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkQ
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro n hn
    obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnQ⟩ := Finset.mem_Icc.mp hnI
    refine ⟨n/d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnQ⟩,
      Nat.mul_div_cancel' hdn⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by simpa using Nat.le_of_dvd hn1 hdn)
  · intro k _
    simp [Nat.cast_mul, mul_inv_rev, mul_comm]

lemma coprimeSixHarmonic_eq (Q : ℕ) :
    coprimeSixHarmonic Q = (harmonic Q : ℝ) -
      (1/2)*(harmonic (Q/2) : ℝ) - (1/3)*(harmonic (Q/3) : ℝ) +
      (1/6)*(harmonic (Q/6) : ℝ) := by
  classical
  have h6 (n : ℕ) : 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
    constructor
    · intro hn
      exact ⟨(by decide : 2 ∣ 6).trans hn, (by decide : 3 ∣ 6).trans hn⟩
    · rintro ⟨h2, h3⟩
      exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3
  have hpoint (n : ℕ) :
      (if ¬ 2 ∣ n ∧ ¬ 3 ∣ n then (n : ℝ)⁻¹ else 0) =
      (n : ℝ)⁻¹ - (if 2 ∣ n then (n : ℝ)⁻¹ else 0) -
        (if 3 ∣ n then (n : ℝ)⁻¹ else 0) + (if 6 ∣ n then (n : ℝ)⁻¹ else 0) := by
    by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;> simp [h2, h3, h6]
  have h2 := harmonic_multiples_sum Q 2 (by omega)
  have h3 := harmonic_multiples_sum Q 3 (by omega)
  have h6sum := harmonic_multiples_sum Q 6 (by omega)
  simp only [Finset.sum_filter] at h2 h3 h6sum
  simp only [coprimeSixHarmonic, Finset.sum_filter, hpoint,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h2, h3, h6sum]
  have hH : (∑ n ∈ Finset.Icc 1 Q, (n : ℝ)⁻¹) = (harmonic Q : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH]
  norm_num

noncomputable def harmonicEnvelope (Q : ℕ) : ℝ :=
  (harmonic Q : ℝ) + (1/2)*(harmonic (Q/2) : ℝ) +
    (1/6)*(harmonic (Q/3) : ℝ) - (1/2)*(harmonic (Q/4) : ℝ) +
    (1/12)*(harmonic (Q/6) : ℝ) - (1/6)*(harmonic (Q/9) : ℝ) -
    (1/12)*(harmonic (Q/12) : ℝ) - (1/12)*(harmonic (Q/18) : ℝ) +
    (1/12)*(harmonic (Q/36) : ℝ)

lemma twoThreeEnvelope_eq (Q : ℕ) : twoThreeEnvelope Q = harmonicEnvelope Q := by
  simp only [twoThreeEnvelope, coprimeSixHarmonic_eq, Nat.div_div_eq_div_mul]
  norm_num only [Nat.reduceMul]
  unfold harmonicEnvelope
  ring

lemma log_two_three_power (a b : ℕ) :
    Real.log ((2 : ℝ)^a * 3^b) = (a : ℝ)*Real.log 2 + (b : ℝ)*Real.log 3 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

lemma harmonicEnvelope_gt_log (Q : ℕ) (hQ : 1440 ≤ Q) :
    Real.log ((Q : ℝ)+1) + 1.07 < harmonicEnvelope Q := by
  have h1 := harmonic_div_lower Q 1 (by omega) (by omega)
  have h2 := harmonic_div_lower Q 2 (by omega) (by omega)
  have h3 := harmonic_div_lower Q 3 (by omega) (by omega)
  have h4 := harmonic_div_upper Q 4 (by omega) (by omega)
  have h6 := harmonic_div_lower Q 6 (by omega) (by omega)
  have h9 := harmonic_div_upper Q 9 (by omega) (by omega)
  have h12 := harmonic_div_upper Q 12 (by omega) (by omega)
  have h18 := harmonic_div_upper Q 18 (by omega) (by omega)
  have h36 := harmonic_div_lower Q 36 (by omega) (by omega)
  have hl4 := log_two_three_power 2 0
  have hl6 := log_two_three_power 1 1
  have hl9 := log_two_three_power 0 2
  have hl12 := log_two_three_power 2 1
  have hl18 := log_two_three_power 1 2
  have hl36 := log_two_three_power 2 2
  norm_num at h1 hl4 hl6 hl9 hl12 hl18 hl36
  unfold harmonicEnvelope
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem G_gt_log_add_107_large (Q : ℕ) (hQ : 1440 ≤ Q) :
    Real.log ((Q : ℝ)+1) + 1.07 < G Q := by
  have h := twoThreeEnvelope_le_G Q (by omega)
  rw [twoThreeEnvelope_eq] at h
  exact (harmonicEnvelope_gt_log Q hQ).trans_le h

end EKG3
