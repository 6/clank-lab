import Beta

namespace LNEDBeta
open Polynomial LNEDPilot
open scoped BigOperators

noncomputable def P (r : ℕ) : ℚ[X] := X ^ 2 *
  ∏ j ∈ Finset.range r, (X ^ 2 - C (((j : ℚ) + 1 / 2) ^ 2))
noncomputable def R (r : ℕ) : ℚ[X] := X *
  ∏ j ∈ Finset.range r, (X - C (((j : ℚ) + 1 / 2) ^ 2))
noncomputable def Q (r : ℕ) : ℚ[X] := X *
  ∏ j ∈ Finset.range r, (X + C (((j : ℚ) + 1 / 2) ^ 2))

/-- The all-power witness endpoint. -/
def HalfWitnessEndpoint : Prop := ∀ r : ℕ,
  (∀ m : ℕ, 1 ≤ m → P r ^ m ∈ VBeta ((r : ℚ) + 1 / 2)) ∧
  (∀ m : ℕ, 1 ≤ m → X * P r ^ m ∉ VBeta ((r : ℚ) + 1 / 2))

lemma A_add (f g : ℚ[X]) : A (f + g) = A f + A g := by
  exact Polynomial.sum_add_index f g _ (by simp) (by intros; exact add_smul _ _ _)
lemma A_smul (c : ℚ) (f : ℚ[X]) : A (c • f) = c • A f := by
  unfold A
  rw [Polynomial.sum_smul_index f c _ (fun i => zero_smul ℚ (H i)), Polynomial.smul_sum]
  simp only [mul_smul]
noncomputable def LL (β : ℚ) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun := L β
  map_add' f g := by simp [L, A_add, eval_add, neg_add, add_div]; ring
  map_smul' c f := by simp [L, A_smul, eval_smul, smul_eq_mul]; ring

lemma L_moment (β : ℚ) (n : ℕ) :
    L β (X ^ n) =
      ((Polynomial.bernoulli (n + 1)).eval β - (Polynomial.bernoulli (n + 1)).eval 0) /
        (((n : ℚ) + 1) * β) := by
  have ha : A (X ^ n) = H n := by
    rw [← monomial_one_right_eq_X_pow]
    simp [A, Polynomial.sum_monomial_index]
  simp only [L, ha, H, eval_mul, eval_C, eval_sub]
  rw [div_mul_eq_div_div]
  ring

lemma L_half_even (k : ℕ) (hk : k ≠ 0) : L (1 / 2) (X ^ (2 * k)) = 0 := by
  rw [L_moment, bernoulli_half_gap_odd k hk, zero_div]

lemma L_half_odd_sign (k : ℕ) : 0 < (-1 : ℚ) ^ (k + 1) * L (1 / 2) (X ^ (2 * k + 1)) := by
  rw [L_moment]
  convert half_odd_moment_strict_sign k using 1 <;> push_cast <;> ring

lemma expand_transform (q : ℚ[X]) (s : ℚ) :
    X * q.comp (C s * X ^ 2) =
      ∑ k ∈ q.support, (q.coeff k * s ^ k) • (X ^ (2 * k + 1) : ℚ[X]) := by
  conv_lhs => rw [← q.sum_C_mul_X_pow_eq]
  simp only [Polynomial.sum_def, sum_comp, mul_comp, C_comp, pow_comp, X_comp,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [smul_eq_C_mul, map_mul, map_pow, mul_pow, ← pow_mul, pow_succ]
  ring

lemma transform_strict_negative (q : ℚ[X]) (hq : q ≠ 0)
    (hc : ∀ k, 0 ≤ q.coeff k) : L (1 / 2) (X * q.comp (-X ^ 2)) < 0 := by
  have h := congrArg (LL (1 / 2)) (expand_transform q (-1))
  simp only [map_sum, map_smul] at h
  change L (1 / 2) (X * q.comp (C (-1) * X ^ 2)) = _ at h
  rw [show C (-1 : ℚ) * X ^ 2 = (-X ^ 2 : ℚ[X]) by simp] at h
  rw [h]
  apply Finset.sum_neg _ (Polynomial.support_nonempty.mpr hq)
  intro k hk
  have hck : 0 < q.coeff k := lt_of_le_of_ne (hc k)
    (Ne.symm (Polynomial.mem_support_iff.mp hk))
  have hs := L_half_odd_sign k
  change q.coeff k * (-1 : ℚ) ^ k * L (1 / 2) (X ^ (2 * k + 1)) < 0
  rw [pow_succ] at hs
  nlinarith [mul_pos hck hs]

def NonnegCoeffs (q : ℚ[X]) : Prop := ∀ k, 0 ≤ q.coeff k
lemma nc_X : NonnegCoeffs (X : ℚ[X]) := by intro k; simp [coeff_X]; split_ifs <;> norm_num
lemma nc_one : NonnegCoeffs (1 : ℚ[X]) := by intro k; simp [coeff_one]; split_ifs <;> norm_num
lemma nc_add (p q : ℚ[X]) (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p + q) := by
  intro k; simpa only [coeff_add] using add_nonneg (hp k) (hq k)
lemma nc_C (c : ℚ) (hc : 0 ≤ c) : NonnegCoeffs (C c) := by
  intro k; simp only [coeff_C]; split_ifs <;> positivity
lemma nc_mul (p q : ℚ[X]) (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p * q) := by
  intro k; rw [coeff_mul]; exact Finset.sum_nonneg (fun t _ => mul_nonneg (hp t.1) (hq t.2))
lemma nc_pow (q : ℚ[X]) (hq : NonnegCoeffs q) (m : ℕ) : NonnegCoeffs (q ^ m) := by
  induction m with
  | zero => simpa using nc_one
  | succ m ih => rw [pow_succ]; exact nc_mul _ _ ih hq
lemma Q_nc (r : ℕ) : NonnegCoeffs (Q r) := by
  apply nc_mul _ _ nc_X
  apply Finset.prod_induction
  · intro a b ha hb; exact nc_mul a b ha hb
  · exact nc_one
  · intro j hj; exact nc_add _ _ nc_X (nc_C _ (sq_nonneg _))
lemma Q_ne_zero (r : ℕ) : Q r ≠ 0 := by
  intro hz
  have he : 0 < (Q r).eval 1 := by
    simp only [Q, eval_mul, eval_X, eval_prod, eval_add, eval_C, one_mul]
    exact Finset.prod_pos (fun j _ => by positivity)
  rw [hz, eval_zero] at he
  exact lt_irrefl _ he

lemma P_eq_R (r : ℕ) : P r = (R r).comp (X ^ 2) := by
  simp [P, R, mul_comp, prod_comp, sub_comp]
lemma R_coeff_zero (r : ℕ) : (R r).coeff 0 = 0 := by simp [R]
lemma Q_flip (r : ℕ) : (Q r).comp (-X ^ 2) = (-1 : ℚ[X]) ^ (r + 1) * P r := by
  simp only [Q, mul_comp, X_comp, prod_comp, add_comp, C_comp]
  have hf : (fun j : ℕ => (-X ^ 2 : ℚ[X]) + C (((j : ℚ) + 1 / 2) ^ 2)) =
      (fun j : ℕ => -(X ^ 2 - C (((j : ℚ) + 1 / 2) ^ 2))) := by funext j; ring
  rw [hf, Finset.prod_neg, Finset.card_range]
  simp only [P, pow_succ]
  ring

lemma even_transform_zero (q : ℚ[X]) (hq : q.coeff 0 = 0) :
    L (1 / 2) (q.comp (X ^ 2)) = 0 := by
  have he : q.comp (X ^ 2) = ∑ k ∈ q.support, q.coeff k • (X ^ (2 * k) : ℚ[X]) := by
    conv_lhs => rw [← q.sum_C_mul_X_pow_eq]
    simp only [Polynomial.sum_def, sum_comp, mul_comp, C_comp, pow_comp, X_comp]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_eq_C_mul, ← pow_mul]
  change LL (1 / 2) _ = 0
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_smul]
  by_cases hk0 : k = 0
  · simp [hk0, hq]
  · change q.coeff k * L (1 / 2) (X ^ (2 * k)) = 0
    rw [L_half_even k hk0, mul_zero]

lemma P_half_power_zero (r m : ℕ) (hm : 1 ≤ m) : L (1 / 2) (P r ^ m) = 0 := by
  rw [P_eq_R, ← pow_comp]
  apply even_transform_zero
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, R_coeff_zero]
  exact zero_pow (by omega)

lemma XP_half_power_ne_zero (r m : ℕ) : L (1 / 2) (X * P r ^ m) ≠ 0 := by
  have hn := transform_strict_negative (Q r ^ m) (pow_ne_zero _ (Q_ne_zero r))
    (nc_pow _ (Q_nc r) m)
  rw [pow_comp, Q_flip, mul_pow] at hn
  intro hz
  have he : X * (((-1 : ℚ[X]) ^ (r + 1)) ^ m * P r ^ m) =
      ((-1 : ℚ) ^ (r + 1)) ^ m • (X * P r ^ m) := by
    simp only [smul_eq_C_mul, map_pow, map_neg, map_one]
    ring
  rw [he] at hn
  change LL (1 / 2) _ < 0 at hn
  rw [map_smul] at hn
  change _ * L (1 / 2) (X * P r ^ m) < 0 at hn
  rw [hz, mul_zero] at hn
  exact lt_irrefl _ hn

lemma P_node_zero (r j : ℕ) (hj : j ∈ Finset.range r) : (P r).eval ((j : ℚ) + 1 / 2) = 0 := by
  simp only [P, eval_mul, eval_prod]
  have hz : (∏ k ∈ Finset.range r,
      (X ^ 2 - C (((k : ℚ) + 1 / 2) ^ 2) : ℚ[X]).eval ((j : ℚ) + 1 / 2)) = 0 := by
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨j, hj, by simp⟩
  rw [hz, mul_zero]

theorem half_witness_all : HalfWitnessEndpoint := by
  intro r
  have hβ : (r : ℚ) + 1 / 2 ≠ 0 := by positivity
  have he (m : ℕ) (hm : 1 ≤ m) :
      (∑ j ∈ Finset.range r, (P r ^ m).eval ((j : ℚ) + 1 / 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [eval_pow, P_node_zero r j hj, zero_pow (by omega)]
  constructor
  · intro m hm
    apply (mem_VBeta_iff_L _ hβ _).mpr
    rw [half_shift_identity, he m hm, P_half_power_zero r m hm]
    ring
  · intro m hm hv
    have hv0 := (mem_VBeta_iff_L _ hβ _).mp hv
    rw [half_shift_identity] at hv0
    have heX : (∑ j ∈ Finset.range r, (X * P r ^ m).eval ((j : ℚ) + 1 / 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [eval_mul, eval_pow, P_node_zero r j hj, zero_pow (by omega), mul_zero]
    rw [heX, mul_zero, add_zero] at hv0
    exact XP_half_power_ne_zero r m ((mul_eq_zero.mp hv0).resolve_left (by positivity))

theorem all_positive_half_not_mathieu : HalfEndpoint := by
  intro r hM
  obtain ⟨N, hN⟩ := hM (P r) (half_witness_all r).1 X 1
  have hin := hN (max N 1) (le_max_left N 1)
  exact (half_witness_all r).2 (max N 1) (le_max_right N 1) (by simpa using hin)

#print axioms half_witness_all
#print axioms all_positive_half_not_mathieu
end LNEDBeta
