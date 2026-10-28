import Claim

namespace LNEDBeta
open Polynomial LNEDPilot
open scoped BigOperators

noncomputable def IBeta (β : ℚ) : Ideal ℚ[X] := Ideal.span {X * (X - C β)}
def VBeta (β : ℚ) : Set ℚ[X] := delta '' (IBeta β : Set ℚ[X])

/-- The rational half-integer and integer endpoints. -/
def HalfEndpoint : Prop := ∀ r : ℕ,
  ¬ TwoSidedMathieu (VBeta ((r : ℚ) + 1 / 2))
def IntegerEndpoint : Prop := ∀ N : ℕ, 0 < N → TwoSidedMathieu (VBeta (N : ℚ))

noncomputable def A (f : ℚ[X]) : ℚ[X] := f.sum fun n c => c • H n
noncomputable def L (β : ℚ) (f : ℚ[X]) : ℚ := -(A f).eval β / β

lemma A_zero (f : ℚ[X]) : (A f).eval 0 = 0 := by
  simp [A, Polynomial.sum_def, eval_finset_sum, H_zero]

lemma delta_A (f : ℚ[X]) : delta (A f) = f := by
  change deltaLinear (f.sum fun n c => c • H n) = f
  simp only [Polynomial.sum_def, map_sum, map_smul]
  simp only [deltaLinear, LinearMap.coe_mk, AddHom.coe_mk, delta_H]
  simpa only [smul_eq_C_mul] using f.sum_C_mul_X_pow_eq

lemma mem_IBeta_iff (β : ℚ) (hβ : β ≠ 0) (h : ℚ[X]) :
    h ∈ IBeta β ↔ h.eval 0 = 0 ∧ h.eval β = 0 := by
  simp only [IBeta, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · rintro ⟨h0, hh⟩
    have hx : (X : ℚ[X]) ∣ h := by
      simpa using (dvd_iff_isRoot.mpr h0 : (X - C (0 : ℚ)) ∣ h)
    obtain ⟨q, hq⟩ := hx
    have hqh : q.eval β = 0 := by
      rw [hq, eval_mul, eval_X] at hh
      exact (mul_eq_zero.mp hh).resolve_left hβ
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqh : (X - C β) ∣ q)
    refine ⟨r, ?_⟩
    rw [hq, hr]
    ring

/-- An equivalence for the actual principal ideal image, not only an annihilator. -/
theorem mem_VBeta_iff (β : ℚ) (hβ : β ≠ 0) (f : ℚ[X]) :
    f ∈ VBeta β ↔ (A f).eval β = 0 := by
  constructor
  · rintro ⟨h, hI, he⟩
    obtain ⟨h0, hh⟩ := (mem_IBeta_iff β hβ h).mp hI
    have hk0 : delta (h - A f) = 0 := by
      rw [delta_sub, he, delta_A, sub_self]
    have hk := delta_kernel_constant (h - A f) hk0
    have hc : (h - A f).eval 0 = 0 := by rw [eval_sub, h0, A_zero, sub_self]
    rw [hc, C_0] at hk
    have heq := sub_eq_zero.mp hk
    rw [← heq]
    exact hh
  · intro hh
    exact ⟨A f, (mem_IBeta_iff β hβ _).mpr ⟨A_zero f, hh⟩, delta_A f⟩

theorem mem_VBeta_iff_L (β : ℚ) (hβ : β ≠ 0) (f : ℚ[X]) :
    f ∈ VBeta β ↔ L β f = 0 := by
  rw [mem_VBeta_iff β hβ, L, _root_.div_eq_zero_iff]
  simp [hβ]

lemma A_eval_step (f : ℚ[X]) (x : ℚ) :
    (A f).eval (x + 1) = (A f).eval x - f.eval x := by
  have h := congrArg (Polynomial.eval x) (delta_A f)
  simp only [delta, phi, eval_sub, eval_comp, eval_add, eval_X, eval_one] at h
  linarith

lemma A_eval_shift (f : ℚ[X]) (x : ℚ) (N : ℕ) :
    (A f).eval (x + N) = (A f).eval x -
      ∑ j ∈ Finset.range N, f.eval (x + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, ← add_assoc, A_eval_step, ih, Finset.sum_range_succ]
    ring

theorem half_shift_identity (f : ℚ[X]) (r : ℕ) :
    L ((r : ℚ) + 1 / 2) f =
      1 / (2 * ((r : ℚ) + 1 / 2)) * L (1 / 2) f +
      1 / ((r : ℚ) + 1 / 2) *
        ∑ j ∈ Finset.range r, f.eval ((j : ℚ) + 1 / 2) := by
  have h := A_eval_shift f (1 / 2) r
  simp only [add_comm (1 / 2 : ℚ)] at h
  rw [L, h, L]
  have hβ : (r : ℚ) + 1 / 2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem integer_image_iff (N : ℕ) (hN : 0 < N) (f : ℚ[X]) :
    f ∈ VBeta (N : ℚ) ↔ ∑ j ∈ Finset.range N, f.eval (j : ℚ) = 0 := by
  have hNZ : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [mem_VBeta_iff _ hNZ]
  have h := A_eval_shift f 0 N
  simp only [zero_add, A_zero, zero_sub] at h
  rw [h, neg_eq_zero]

theorem positive_integer_mathieu : IntegerEndpoint := by
  intro N hN a ha b c
  have h2 := (integer_image_iff N hN (a ^ 2)).mp (ha 2 (by omega))
  simp only [eval_pow] at h2
  have hv : ∀ j ∈ Finset.range N, a.eval (j : ℚ) = 0 := by
    intro j hj
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.range N) => sq_nonneg (a.eval (j : ℚ)))).mp h2 j hj
    exact pow_eq_zero hz
  refine ⟨1, ?_⟩
  intro m hm
  apply (integer_image_iff N hN _).mpr
  apply Finset.sum_eq_zero
  intro j hj
  simp [hv j hj, Nat.ne_of_gt (show 0 < m by omega)]

/-- The strict sign of the even Bernoulli half-gap, for every positive index. -/
theorem half_gap_strict_sign (k : ℕ) (hk : k ≠ 0) :
    0 < (-1 : ℚ) ^ k *
      ((Polynomial.bernoulli (2 * k)).eval (1 / 2 : ℚ) -
        (Polynomial.bernoulli (2 * k)).eval 0) := by
  have hs0 := hasSum_one_div_nat_pow_mul_cos hk
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hsh := hasSum_one_div_nat_pow_mul_cos hk
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  let f : ℕ → ℝ := fun n =>
    1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * (0 : ℝ)) -
    1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * (1 / 2 : ℝ))
  have hs := hs0.sub hsh
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    rw [mul_zero, Real.cos_zero, mul_one]
    have ha : 0 ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
    have hc := Real.cos_le_one (2 * Real.pi * (n : ℝ) * (1 / 2 : ℝ))
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hc)]
  have hf1 : 0 < f 1 := by
    dsimp [f]
    norm_num only [Nat.cast_one, one_pow, div_one, mul_one, mul_zero,
      Real.cos_zero, one_mul]
    rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.cos_pi]
    norm_num
  have hp := hs.summable.tsum_pos hf 1 hf1
  rw [hs.tsum_eq] at hp
  change 0 < _ * bernoulliFun (2 * k) 0 - _ * bernoulliFun (2 * k) (1 / 2 : ℝ) at hp
  have hscale : 0 < (2 * Real.pi) ^ (2 * k) / 2 / (Nat.factorial (2 * k) : ℝ) := by
    positivity
  have hprod : 0 < ((2 * Real.pi) ^ (2 * k) / 2 / (Nat.factorial (2 * k) : ℝ)) *
      ((-1 : ℝ) ^ k * (bernoulliFun (2 * k) (1 / 2 : ℝ) - bernoulliFun (2 * k) 0)) := by
    convert hp using 1 <;> simp only [pow_succ] <;> ring
  have hsign := (mul_pos_iff_of_pos_left hscale).mp hprod
  have hq : bernoulliFun (2 * k) (1 / 2 : ℝ) =
      (((Polynomial.bernoulli (2 * k)).eval (1 / 2 : ℚ) : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k) (1 / 2)
  have hz : bernoulliFun (2 * k) 0 =
      (((Polynomial.bernoulli (2 * k)).eval 0 : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k) 0
  rw [hq, hz] at hsign
  exact_mod_cast hsign

theorem half_odd_moment_strict_sign (k : ℕ) :
    0 < (-1 : ℚ) ^ (k + 1) *
      (((Polynomial.bernoulli (2 * k + 2)).eval (1 / 2 : ℚ) -
        (Polynomial.bernoulli (2 * k + 2)).eval 0) / (k + 1 : ℚ)) := by
  have hs := half_gap_strict_sign (k + 1) (by omega)
  have hd : (0 : ℚ) < (k + 1 : ℚ) := by positivity
  rw [show 2 * (k + 1) = 2 * k + 2 by omega] at hs
  simpa only [mul_div_assoc] using div_pos hs hd

#print axioms mem_VBeta_iff
#print axioms positive_integer_mathieu
#print axioms half_odd_moment_strict_sign
end LNEDBeta
