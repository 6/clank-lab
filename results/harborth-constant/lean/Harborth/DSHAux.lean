import Mathlib

/-!
# Helper lemmas for the Dias da Silva–Hamidoune theorem

The polynomial method of Alon–Nathanson–Ruzsa. For exponents `t : Fin h →₀ ℕ` with
`∑ t = m + ∑ i`, the coefficient of `x^t` in `det (vandermonde X) * (∑ X i) ^ m`, times
`∏ (t j)!`, equals `m! * det (vandermonde t)`.
-/

namespace Harborth.DSHAux

open MvPolynomial Finset

/-- The exponent vector of the monomial `∏ i, X (σ i) ^ i`. -/
noncomputable def permExp {h : ℕ} (σ : Equiv.Perm (Fin h)) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => ((σ⁻¹ j : Fin h) : ℕ))

lemma permExp_apply {h : ℕ} (σ : Equiv.Perm (Fin h)) (j : Fin h) :
    permExp σ j = ((σ⁻¹ j : Fin h) : ℕ) := rfl

lemma sum_permExp {h : ℕ} (σ : Equiv.Perm (Fin h)) :
    ∑ j, permExp σ j = ∑ i : Fin h, (i : ℕ) := by
  simp only [permExp_apply]
  exact Equiv.sum_comp σ⁻¹ (fun i : Fin h => (i : ℕ))

lemma prod_X_pow_perm {R : Type*} [CommRing R] {h : ℕ} (σ : Equiv.Perm (Fin h)) :
    (∏ i, (X (σ i) : MvPolynomial (Fin h) R) ^ (i : ℕ)) = monomial (permExp σ) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  rw [← Equiv.prod_comp σ (fun j => (X j : MvPolynomial (Fin h) R) ^ permExp σ j)]
  simp [permExp_apply]

/-- The vandermonde determinant in the variables. -/
lemma det_vandermonde_X {R : Type*} [CommRing R] {h : ℕ} :
    (Matrix.vandermonde (X : Fin h → MvPolynomial (Fin h) R)).det =
      ∑ σ : Equiv.Perm (Fin h), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) R) *
        monomial (permExp σ) 1 := by
  rw [Matrix.det_apply']
  simp only [Matrix.vandermonde_apply, prod_X_pow_perm]

/-- The arithmetic identity behind each term. -/
lemma nat_identity {h : ℕ} (t e : Fin h →₀ ℕ) (m : ℕ) (hsum : ∑ j, t j = m + ∑ j, e j) :
    (if e ≤ t then (if (t - e).sum (fun _ n => n) = m then (t - e).multinomial else 0) else 0) *
        ∏ j, (t j).factorial =
      m.factorial * ∏ j, (t j).descFactorial (e j) := by
  split_ifs with h1 h2
  · rw [Finsupp.multinomial_eq_of_support_subset (subset_univ _)]
    rw [Finsupp.sum_fintype _ _ (by simp)] at h2
    have hfac : ∏ j, (t j).factorial =
        (∏ j, ((t - e) j).factorial) * ∏ j, (t j).descFactorial (e j) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      rw [Finsupp.tsub_apply, Nat.factorial_mul_descFactorial (h1 j)]
    rw [hfac, ← mul_assoc, mul_comm _ (∏ j, ((t - e) j).factorial), Nat.multinomial_spec, h2]
  · exfalso
    apply h2
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.tsub_apply]
    rw [sum_tsub_distrib _ (fun j _ => h1 j)]
    omega
  · rw [Finsupp.le_def] at h1
    push Not at h1
    obtain ⟨j, hj⟩ := h1
    rw [zero_mul, prod_eq_zero (f := fun j => (t j).descFactorial (e j)) (mem_univ j)
      ((Nat.descFactorial_eq_zero_iff_lt).2 hj), mul_zero]

lemma coeff_monomial_mul_sum_pow {R : Type*} [CommRing R] {h : ℕ} (e t : Fin h →₀ ℕ) (m : ℕ) :
    (monomial e (1 : R) * (∑ i, X i) ^ m).coeff t =
      if e ≤ t then (if (t - e).sum (fun _ n => n) = m then ((t - e).multinomial : R) else 0)
      else 0 := by
  rw [coeff_monomial_mul', coeff_sum_X_pow_of_fintype, one_mul]
  split_ifs <;> simp

/-- The coefficient identity: `coeff t (V * (∑ X i) ^ m) * ∏ (t j)! = m! * det (vandermonde t)`. -/
lemma coeff_vandermonde_mul_sum_pow {R : Type*} [CommRing R] [IsDomain R] {h : ℕ}
    (t : Fin h →₀ ℕ) (m : ℕ) (ht : ∑ j, t j = m + ∑ i : Fin h, (i : ℕ)) :
    ((Matrix.vandermonde (X : Fin h → MvPolynomial (Fin h) R)).det * (∑ i, X i) ^ m).coeff t *
        ∏ j, ((t j).factorial : R) =
      (m.factorial : R) * (Matrix.vandermonde (fun j => (t j : R))).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde _ (fun i => descPochhammer R i)
    (fun i => descPochhammer_natDegree R i) (fun i => monic_descPochhammer R i)]
  rw [det_vandermonde_X, Matrix.det_apply', sum_mul, coeff_sum, sum_mul, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
  have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) R) = C ((Equiv.Perm.sign σ : ℤ) : R) := by
    simp
  rw [mul_assoc, hC, coeff_C_mul, coeff_monomial_mul_sum_pow]
  have hre : ∏ i, (((t (σ i)).descFactorial (i : ℕ) : ℕ) : R) =
      ∏ j, (((t j).descFactorial (permExp σ j) : ℕ) : R) := by
    rw [← Equiv.prod_comp σ (fun j => (((t j).descFactorial (permExp σ j) : ℕ) : R))]
    simp [permExp_apply]
  have key := congrArg (Nat.cast : ℕ → R) (nat_identity t (permExp σ) m (by rw [ht, sum_permExp]))
  push_cast [apply_ite (Nat.cast : ℕ → R)] at key
  rw [hre, mul_assoc, key]
  ring

lemma isHomogeneous_det_vandermonde_X {R : Type*} [CommRing R] {h : ℕ} :
    (Matrix.vandermonde (X : Fin h → MvPolynomial (Fin h) R)).det.IsHomogeneous
      (∑ i : Fin h, (i : ℕ)) := by
  rw [det_vandermonde_X]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [show ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) R) =
    C ((Equiv.Perm.sign σ : ℤ) : R) by simp]
  exact (isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_sum, sum_permExp])).C_mul _

lemma isHomogeneous_vandermonde_mul_sum_pow {R : Type*} [CommRing R] {h : ℕ} (l : ℕ) :
    ((Matrix.vandermonde (X : Fin h → MvPolynomial (Fin h) R)).det * (∑ i, X i) ^ l).IsHomogeneous
      (∑ i : Fin h, (i : ℕ) + l) := by
  have hS : (∑ i, X i : MvPolynomial (Fin h) R).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X R i
  simpa using isHomogeneous_det_vandermonde_X.mul (hS.pow l)

/-- The core of the polynomial method: if `t` is injective with `t i < |A|`, and
`∑ t = m + ∑ i` with `m < p`, then there are more than `m` sums of `h`-subsets of `A`. -/
theorem core {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) (h : ℕ) (t : Fin h → ℕ)
    (ht_inj : Function.Injective t) (ht_lt : ∀ i, t i < A.card) (m : ℕ)
    (hm : ∑ i, t i = m + ∑ i : Fin h, (i : ℕ)) (hmp : m < p) :
    m + 1 ≤ ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)).card := by
  classical
  set C := (A.powersetCard h).image (fun B => ∑ x ∈ B, x) with hCdef
  by_contra hlt
  push Not at hlt
  have hCm : C.card ≤ m := by omega
  set S : MvPolynomial (Fin h) (ZMod p) := ∑ i, X i with hS
  set V : MvPolynomial (Fin h) (ZMod p) := (Matrix.vandermonde X).det with hV
  set q : Polynomial (ZMod p) :=
    (∏ c ∈ C, (Polynomial.X - Polynomial.C c)) * Polynomial.X ^ (m - C.card) with hq
  have hqmon : q.Monic :=
    (Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C c).mul
      (Polynomial.monic_X_pow _)
  have hqdeg : q.natDegree = m := by
    rw [hq, (Polynomial.monic_prod_of_monic _ _ fun c _ =>
      Polynomial.monic_X_sub_C c).natDegree_mul (Polynomial.monic_X_pow _),
      Polynomial.natDegree_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C c]
    simp only [Polynomial.natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one,
      Polynomial.natDegree_X_pow]
    omega
  set f := V * Polynomial.aeval S q with hf
  have hfsum : f = ∑ l ∈ range (m + 1), q.coeff l • (V * S ^ l) := by
    rw [hf, Polynomial.aeval_eq_sum_range, hqdeg, mul_sum]
    simp only [mul_smul_comm]
  set T : Fin h →₀ ℕ := Finsupp.equivFunOnFinite.symm t with hT
  have hTapp : ∀ i, T i = t i := fun i => rfl
  have hTdeg : T.degree = ∑ i : Fin h, (i : ℕ) + m := by
    rw [Finsupp.degree_eq_sum]; simp only [hTapp]; omega
  have hcoeff_eq : f.coeff T = (V * S ^ m).coeff T := by
    rw [hfsum, coeff_sum, sum_eq_single m]
    · have hqm : q.coeff m = 1 := by rw [← hqdeg]; exact hqmon.coeff_natDegree
      rw [coeff_smul, hqm, one_smul]
    · intro l _ hl
      rw [coeff_smul, (isHomogeneous_vandermonde_mul_sum_pow l).coeff_eq_zero, smul_zero]
      rw [hTdeg]; omega
    · intro hm'; simp at hm'
  have hAp : A.card ≤ p := by simpa [ZMod.card] using A.card_le_univ
  have hcoeff : f.coeff T ≠ 0 := by
    intro h0
    have key := coeff_vandermonde_mul_sum_pow (R := ZMod p) T m (by simp only [hTapp]; exact hm)
    rw [← hV, ← hS, ← hcoeff_eq, h0, zero_mul] at key
    have hfac : (m.factorial : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
      omega
    have hdet : (Matrix.vandermonde (fun j => (T j : ZMod p))).det ≠ 0 := by
      rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
      rintro ⟨i, j, hij, hne⟩
      simp only [hTapp, ZMod.natCast_eq_natCast_iff'] at hij
      rw [Nat.mod_eq_of_lt ((ht_lt i).trans_le hAp), Nat.mod_eq_of_lt ((ht_lt j).trans_le hAp)]
        at hij
      exact hne (ht_inj hij)
    exact mul_ne_zero hfac hdet key.symm
  have hdeg : f.totalDegree = T.degree := by
    apply le_antisymm
    · rw [hfsum, hTdeg]
      refine totalDegree_finsetSum_le fun l hl => ?_
      refine (totalDegree_smul_le _ _).trans ?_
      refine (isHomogeneous_vandermonde_mul_sum_pow l).totalDegree_le.trans ?_
      simp only [mem_range] at hl
      omega
    · have := le_totalDegree (mem_support_iff.2 hcoeff)
      rwa [Finsupp.degree_eq_sum, ← Finsupp.sum_fintype T (fun _ e => e) (by simp)]
  obtain ⟨s, hsA, hs⟩ := combinatorial_nullstellensatz_exists_eval_nonzero f T hcoeff hdeg
    (fun _ => A) (fun i => by rw [hTapp]; exact ht_lt i)
  apply hs
  have hfeval : eval s f = (Matrix.vandermonde s).det *
      ((∏ c ∈ C, (∑ i, s i - c)) * (∑ i, s i) ^ (m - C.card)) := by
    rw [hf, hV, eval_mul, RingHom.map_det]
    congr 1
    · congr 1
      ext i j
      simp [Matrix.vandermonde_apply]
    · simp [hq, hS, map_prod]
  rw [hfeval]
  by_cases hinj : Function.Injective s
  · have hmem : ∑ i, s i ∈ C := by
      rw [hCdef, mem_image]
      refine ⟨univ.image s, ?_, ?_⟩
      · rw [mem_powersetCard, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
        exact ⟨fun x hx => by
          obtain ⟨i, -, rfl⟩ := mem_image.1 hx
          exact hsA i, rfl⟩
      · rw [sum_image fun i _ j _ hij => hinj hij]
    rw [prod_eq_zero hmem (sub_self _), zero_mul, mul_zero]
  · have hdet : (Matrix.vandermonde s).det = 0 := by
      rw [Matrix.det_vandermonde_eq_zero_iff]
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hij, hne⟩ := hinj
      exact ⟨i, j, hij, hne⟩
    rw [hdet, zero_mul]

lemma sum_fin_val_succ (h : ℕ) :
    ∑ i : Fin (h + 1), (i : ℕ) = ∑ i : Fin h, (i : ℕ) + h := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, zero_add]

/-- Distinct exponents below `k` with any prescribed excess `m ≤ h (k - h)` over `∑ i`. -/
lemma exists_exponents (h : ℕ) : ∀ k m : ℕ, h ≤ k → m ≤ h * (k - h) →
    ∃ t : Fin h → ℕ, Function.Injective t ∧ (∀ i, t i < k) ∧
      ∑ i, t i = m + ∑ i : Fin h, (i : ℕ) := by
  induction h with
  | zero =>
    intro k m _ hm
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simp only [zero_mul, Nat.le_zero] at hm
    simp [hm]
  | succ h ih =>
    intro k m hk hm
    set r := min (k - (h + 1)) m with hr
    have hr1 : r ≤ k - (h + 1) := min_le_left _ _
    have hr2 : r ≤ m := min_le_right _ _
    have hmr : m - r ≤ h * (h + r - h) := by
      rw [Nat.add_sub_cancel_left]
      rcases min_cases (k - (h + 1)) m with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [← hr] at h1
        have : (h + 1) * (k - (h + 1)) = h * (k - (h + 1)) + (k - (h + 1)) := by ring
        rw [h1]
        omega
      · omega
    obtain ⟨t, hinj, hlt, hsum⟩ := ih (h + r) (m - r) (by omega) hmr
    refine ⟨Fin.cons (h + r) t, ?_, ?_, ?_⟩
    · refine Fin.cons_injective_iff.2 ⟨?_, hinj⟩
      rintro ⟨i, hi⟩
      exact (hlt i).ne hi
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ]; have := hlt i; omega
    · rw [Fin.sum_univ_succ, sum_fin_val_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega

end Harborth.DSHAux
