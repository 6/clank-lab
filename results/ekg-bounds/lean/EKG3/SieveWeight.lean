import OAI.NumberTheory.Ostmann.Supply.PrimeSetSupportSieve
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

namespace EKG3
open scoped BigOperators
open OAI.Ostmann

noncomputable def sievePrimes (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter Nat.Prime

noncomputable def sieveWeight (U : Finset ℕ) : ℝ :=
  ∏ p ∈ U, ((p : ℝ) - 1)⁻¹

noncomputable def G (Q : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, (Nat.totient q : ℝ)⁻¹

lemma reciprocal_smooth_hasSum (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    HasSum (fun k : Nat.factoredNumbers U => (k.val : ℝ)⁻¹)
      (∏ p ∈ U, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hpgeom (p : ℕ) (hp : p.Prime) :
      HasSum (fun n : ℕ => ((p ^ n : ℕ) : ℝ)⁻¹) (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hnorm : ‖(p : ℝ)⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (inv_lt_one₀ (by positivity)).mpr hpR
    simpa only [Nat.cast_pow, inv_pow] using hasSum_geometric_of_norm_lt_one hnorm
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ)⁻¹) (by simp)
    (fun {m n} _ => by simp [Nat.cast_mul, mul_inv_rev, mul_comm])
    (fun {p} hp => (hpgeom p hp).summable.norm) U
  convert h.2 using 1
  rw [Finset.filter_true_of_mem hU]
  apply Finset.prod_congr rfl
  intro p hp
  exact (hpgeom p (hU p hp)).tsum_eq.symm

lemma reciprocal_smooth_scaled_hasSum (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    HasSum (fun k : Nat.factoredNumbers U =>
      (((∏ p ∈ U, p : ℕ) : ℝ) * (k.val : ℝ))⁻¹) (sieveWeight U) := by
  have h := (reciprocal_smooth_hasSum U hU).mul_left
    (((∏ p ∈ U, p : ℕ) : ℝ)⁻¹)
  simp only [mul_inv_rev, mul_comm] at h ⊢
  convert h using 1
  simp only [Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hU p hp).one_lt
  field_simp

lemma prime_product_coprime (p : ℕ) (U : Finset ℕ) (hp : p.Prime)
    (hU : ∀ q ∈ U, q.Prime) (hpU : p ∉ U) : p.Coprime (∏ q ∈ U, q) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  exact (Nat.coprime_primes hp (hU q hq)).mpr (fun he => hpU (he ▸ hq))

lemma prime_product_squarefree (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    Squarefree (∏ p ∈ U, p) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert p U hpU ih =>
    have hp := hU p (Finset.mem_insert_self _ _)
    have hU' : ∀ q ∈ U, q.Prime := fun q hq => hU q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpU, Nat.squarefree_mul (prime_product_coprime p U hp hU' hpU)]
    exact ⟨hp.squarefree, ih hU'⟩

lemma sieveWeight_eq_totient (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    sieveWeight U = (Nat.totient (∏ p ∈ U, p) : ℝ)⁻¹ := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [sieveWeight]
  | @insert p U hpU ih =>
    have hp := hU p (Finset.mem_insert_self _ _)
    have hU' : ∀ q ∈ U, q.Prime := fun q hq => hU q (Finset.mem_insert_of_mem hq)
    rw [sieveWeight, Finset.prod_insert hpU]
    change ((p : ℝ) - 1)⁻¹ * sieveWeight U = _
    rw [ih hU', Finset.prod_insert hpU,
      Nat.totient_mul (prime_product_coprime p U hp hU' hpU), Nat.totient_prime hp,
      Nat.cast_mul, Nat.cast_sub hp.one_le]
    simp [mul_inv_rev, mul_comm]

lemma subset_weight_eq_G (Q : ℕ) :
    (∑ U ∈ boundedSieveSubsets (sievePrimes Q) Q, sieveWeight U) = G Q := by
  classical
  apply Finset.sum_bij (fun U _ => ∏ p ∈ U, p)
  · intro U hU
    obtain ⟨hUP, hprod⟩ := Finset.mem_filter.mp hU
    have hpr : ∀ p ∈ U, p.Prime := fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp hUP hp)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Finset.prod_pos (fun p hp => (hpr p hp).pos), hprod⟩,
      prime_product_squarefree U hpr⟩
  · intro U hU V hV he
    have hpr (T : Finset ℕ) (hT : T ∈ boundedSieveSubsets (sievePrimes Q) Q) :
        ∀ p ∈ T, p.Prime := fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hp)).2
    have := congrArg Nat.primeFactors he
    simpa [Nat.primeFactors_prod (hpr U hU), Nat.primeFactors_prod (hpr V hV)] using this
  · intro q hq
    obtain ⟨hqI, hsq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hqI
    refine ⟨q.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hprime.two_le, (Nat.le_of_dvd hq1 hdvd).trans hqQ⟩, hprime⟩
    · simpa [Nat.prod_primeFactors_of_squarefree hsq] using hqQ
  · intro U hU
    exact sieveWeight_eq_totient U (fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp)).2)

lemma reciprocal_primeFactors_fiber_le (U : Finset ℕ)
    (hU : ∀ p ∈ U, p.Prime) (Q : ℕ) :
    (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => n.primeFactors = U), (n : ℝ)⁻¹) ≤
      sieveWeight U := by
  classical
  let F := (Finset.Icc 1 Q).filter (fun n => n.primeFactors = U)
  let q := ∏ p ∈ U, p
  have hnpos (n : ℕ) (hn : n ∈ F) : 0 < n :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hd (n : ℕ) (hn : n ∈ F) : q ∣ n := by
    have he := (Finset.mem_filter.mp hn).2
    simpa only [he] using Nat.prod_primeFactors_dvd n
  have hs (n : ℕ) (hn : n ∈ F) : n / q ∈ Nat.factoredNumbers U := by
    apply Nat.mem_factoredNumbers_of_dvd _ (Nat.div_dvd_of_dvd (hd n hn))
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (hnpos n hn).ne'
    exact (Finset.mem_filter.mp hn).2.le
  let f : F → Nat.factoredNumbers U := fun n => ⟨n.val / q, hs n.val n.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he := congrArg (fun k : Nat.factoredNumbers U => q * k.val) hab
    simpa only [f, Nat.mul_div_cancel' (hd a.val a.property),
      Nat.mul_div_cancel' (hd b.val b.property)] using he
  let T := F.attach.image f
  have hsum : (∑ k ∈ T, (((q : ℝ) * (k.val : ℝ))⁻¹)) =
      ∑ n ∈ F, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image (fun _ _ _ _ he => hf he)]
    have he : (∑ n ∈ F.attach, (((q : ℝ) * ((f n).val : ℝ))⁻¹)) =
        ∑ n ∈ F.attach, (n.val : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n _
      have hnq := Nat.mul_div_cancel' (hd n.val n.property)
      change ((q : ℝ) * ((n.val / q : ℕ) : ℝ))⁻¹ = (n.val : ℝ)⁻¹
      rw [← Nat.cast_mul, hnq]
    rw [he]
    exact Finset.sum_attach F (fun n : ℕ => (n : ℝ)⁻¹)
  have h := reciprocal_smooth_scaled_hasSum U hU
  have hb := h.summable.sum_le_tsum T (fun _ _ => by positivity)
  rw [h.tsum_eq] at hb
  rw [hsum] at hb
  exact hb

lemma primeFactors_mem_boundedSieveSubsets {n Q : ℕ}
    (hn : n ∈ Finset.Icc 1 Q) :
    n.primeFactors ∈ boundedSieveSubsets (sievePrimes Q) Q := by
  obtain ⟨hn1, hnQ⟩ := Finset.mem_Icc.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
  · intro p hp
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hpp.two_le, (Nat.le_of_dvd hn1 hpn).trans hnQ⟩, hpp⟩
  · exact (Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)).trans hnQ

/-- Partitioning integers by their prime support bounds each fiber by its
convergent finite Euler product. No asymptotic estimate is used. -/
theorem harmonic_le_G (Q : ℕ) : (harmonic Q : ℝ) ≤ G Q := by
  classical
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => primeFactors_mem_boundedSieveSubsets hn) (fun n : ℕ => (n : ℝ)⁻¹)]
  rw [← subset_weight_eq_G]
  apply Finset.sum_le_sum
  intro U hU
  exact reciprocal_primeFactors_fiber_le U (fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp)).2) Q

theorem log_lt_harmonic (Q : ℕ) (hQ : 1 ≤ Q) : Real.log Q < (harmonic Q : ℝ) := by
  have hpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlt : (Q : ℝ) < (Q + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self Q
  exact (Real.log_lt_log hpos hlt).trans_le (log_add_one_le_harmonic Q)

theorem log_lt_G (Q : ℕ) (hQ : 1 ≤ Q) : Real.log Q < G Q :=
  (log_lt_harmonic Q hQ).trans_le (harmonic_le_G Q)

end EKG3
