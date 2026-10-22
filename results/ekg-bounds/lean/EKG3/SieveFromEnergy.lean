import EKG3.RefinedFareySieve

/-! The positive-energy argument of the Apache-2.0 OAI support sieve,
generalized to accept a bound on its normalized additive energy. The proof
bodies below are adapted from the three named upstream supply modules;
see vendor/OAI/NOTICE for source commit and licence. -/
namespace EKG3
open scoped Classical BigOperators
open OAI.Ostmann

theorem prime_subset_sieve_bound_from_energy
    {n M Q : ℕ} {C : ℝ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (henergy : (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤ C / A.card) :
    (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
      centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      C / A.card := by
  have hpos (R : Finset (Fin n)) : 0 < ∏ i ∈ R, p i :=
    Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have he (R) (hR : R ∈ G) :
      (∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) =
      intervalSetReducedEnergy A J (∏ i ∈ R, p i) := by
    let : NeZero (∏ i ∈ R, p i) := ⟨(hpos R).ne'⟩
    rw [intervalSetReducedEnergy_eq_unitFrequencyEnergy]
    exact (subset_reduced_energy_expansion p S R hc A
      (fun x => J + (x.val : ℤ)) (ha R hR)).symm
  calc
    _ = ∑ R ∈ G, intervalSetReducedEnergy A J (∏ i ∈ R, p i) :=
      Finset.sum_congr rfl he
    _ = ∑ q ∈ G.image (fun R => ∏ i ∈ R, p i), intervalSetReducedEnergy A J q := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => prime_subset_product_injective p hc h
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_Icc.mpr ⟨hpos R, hprod R hR⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg A J q
    _ ≤ _ := henergy


theorem prime_subset_main_term_from_energy
    {n M Q : ℕ} {C : ℝ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (G : Finset (Finset (Fin n))) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (henergy : (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤ C / A.card) :
    (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S i).card - 1)) ≤
      C / A.card := by
  apply le_trans _ (prime_subset_sieve_bound_from_energy p hc S G hQ hM A hA J hprod ha henergy)
  apply Finset.sum_le_sum
  intro R hR
  have hnonneg (T : Finset (Fin n)) (_hT : T ∈ R.powerset) :
      0 ≤ subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i))) :=
    mul_nonneg (subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i))
      (centeredSubsetEnergy_nonneg p S T A _)
  have h := Finset.single_le_sum hnonneg (show ∅ ∈ R.powerset by simp)
  rw [centeredSubsetEnergy_empty p S A hA, mul_one] at h
  simpa only [subsetSieveCoefficient, Finset.prod_empty, one_mul, Finset.sdiff_empty] using h


theorem prime_set_support_sieve_from_energy {M Q : ℕ} {C : ℝ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : ∀ p : ℕ, Finset (ZMod p))
    (hS : ∀ p ∈ P, (S p).Nonempty) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ p ∈ P, ((J + (x.val : ℤ) : ℤ) : ZMod p) ∈ S p)
    (henergy : (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤ C / A.card) :
    (∑ U ∈ boundedSieveSubsets P Q, ∏ p ∈ U, ((p : ℝ) / (S p).card - 1)) ≤
      C / A.card := by
  let e : Fin P.card ≃ P := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin P).symm
  let p : Fin P.card → ℕ := fun i => (e i).val
  have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hmem (i : Fin P.card) : p i ∈ P := (e i).property
  have hcover : ∀ q ∈ P, ∃ i : Fin P.card, p i = q := by
    intro q hq
    refine ⟨e.symm ⟨q, hq⟩, ?_⟩
    simp only [p, Equiv.apply_symm_apply]
  let : ∀ i, Fact (p i).Prime := fun i => ⟨hP _ (hmem i)⟩
  have hc : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hP _ (hmem i)) (hP _ (hmem j))).mpr
      (fun he => hij (hinj he))
  let G := (Finset.univ : Finset (Fin P.card)).powerset.filter
    (fun R => (∏ i ∈ R, p i) ≤ Q)
  have hGprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q := fun _ hR => (Finset.mem_filter.mp hR).2
  have hbound := prime_subset_main_term_from_energy p hc (fun i => S (p i))
    (fun i => hS _ (hmem i)) G hQ hM A hA J hGprod
    (fun _ _ x hx i _ => ha x hx (p i) (hmem i)) henergy
  have hsum : (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S (p i)).card - 1)) =
      ∑ U ∈ boundedSieveSubsets P Q, ∏ q ∈ U, ((q : ℝ) / (S q).card - 1) := by
    apply Finset.sum_bij (fun R _ => R.image p)
    · intro R hR
      have hprod : (∏ q ∈ R.image p, q) = ∏ i ∈ R, p i := by
        rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro q hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
        exact hmem i
      · rw [hprod]
        exact hGprod R hR
    · intro R _ T _ he
      exact Finset.image_injective hinj he
    · intro U hU
      have hUP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      let R := (Finset.univ : Finset (Fin P.card)).filter fun i => p i ∈ U
      have himage : R.image p = U := by
        ext q
        constructor
        · intro hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          exact (Finset.mem_filter.mp hi).2
        · intro hq
          obtain ⟨i, hi⟩ := hcover q (hUP hq)
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa only [hi] using hq⟩, hi⟩
      refine ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩, himage⟩
      have he : (∏ q ∈ U, q) = ∏ i ∈ R, p i := by
        rw [← himage, Finset.prod_image]; exact fun _ _ _ _ hij => hinj hij
      rw [← he]
      exact (Finset.mem_filter.mp hU).2
    · intro R _
      rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
  rwa [hsum] at hbound


theorem additiveSieve_probability_bound_refined
    {M Q : ℕ} (hQ : 2 ≤ Q) (A : Finset (Fin M))
    (hA : A.Nonempty) (J : ℤ) :
    (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2 - 1) / A.card := by
  let c : Fin M → ℂ := fun n => if n ∈ A then 1 else 0
  have hc (q h : ℕ) : additiveSieveSum c J q h = intervalSetExponentialSum A J q h := by
    simp [additiveSieveSum, intervalSetExponentialSum, c]
  have hn : (∑ n, ‖c n‖ ^ 2) = (A.card : ℝ) := by
    have he (n : Fin M) : ‖c n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      by_cases h : n ∈ A <;> simp [c, h]
    simp [he]
  have hh := publishedAdditiveLargeSieve_refined M Q hQ J c
  simp only [hc, hn] at hh
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    _ = ((A.card : ℝ)⁻¹) ^ 2 *
        ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
          ‖intervalSetExponentialSum A J q h‖ ^ 2 := by
      simp only [intervalSetReducedEnergy, norm_mul, norm_inv, Complex.norm_natCast,
        mul_pow, Finset.mul_sum]
    _ ≤ ((A.card : ℝ)⁻¹) ^ 2 * (((M : ℝ) + (Q : ℝ) ^ 2 - 1) * A.card) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by field_simp

end EKG3
