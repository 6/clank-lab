import Unit

namespace LNEDExtension
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

noncomputable def scale (c : K) (p : K[X]) : K[X] := p.comp (C c⁻¹ * X)
noncomputable def scaledNormalized (c : K) (n : ℕ) : K[X] :=
  C (c ^ n) * scale c (normalized n)

lemma diff_C_mul (c a : K) (p : K[X]) :
    diff c (C a * p) = C a * diff c p := by
  simp only [diff, shift, mul_comp, C_comp]
  ring

lemma diff_scale (c : K) (hc : c ≠ 0) (p : K[X]) :
    diff c (scale c p) = scale c (diff 1 p) := by
  have h : (C c⁻¹ * X).comp (X + C c) = (X + C (1 : K)).comp (C c⁻¹ * X) := by
    simp only [mul_comp, C_comp, X_comp, add_comp]
    rw [mul_add, ← C_mul, inv_mul_cancel₀ hc, C_1]
  simp only [diff, shift, scale, sub_comp, comp_assoc]
  rw [h]

lemma scaled_diff (c : K) (hc : c ≠ 0) (n : ℕ) :
    diff c (scaledNormalized c n) = (X : K[X]) ^ n := by
  rw [scaledNormalized, diff_C_mul, diff_scale c hc, normalized_diff]
  simp only [scale, pow_comp, X_comp, mul_pow, ← C_pow]
  rw [← mul_assoc, ← C_mul, ← mul_pow, mul_inv_cancel₀ hc, one_pow, C_1, one_mul]

lemma scaled_zero (c : K) (n : ℕ) : (scaledNormalized c n).eval 0 = 0 := by
  simp [scaledNormalized, scale, normalized_zero]

lemma scaled_half (c : K) (hc : c ≠ 0) (n : ℕ) :
    (scaledNormalized c n).eval (c * half) =
      c ^ n * algebraMap ℚ K ((LNEDPilot.H n).eval (1 / 2 : ℚ)) := by
  simp only [scaledNormalized, scale, eval_mul, eval_C, eval_comp, eval_X]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [half, normalized_eval]

lemma kernel_constant_shift (c : K) (hc : c ≠ 0) (p : K[X]) (hd : diff c p = 0) :
    p = C (p.eval 0) := by
  have hp : p = shift c p := sub_eq_zero.mp hd
  have hperiod (q : K) : p.eval (q + c) = p.eval q := by
    have hh := congrArg (Polynomial.eval q) hp
    simpa only [shift, eval_comp, eval_add, eval_X, eval_C] using hh.symm
  have hnat : ∀ n : ℕ, p.eval ((n : K) * c) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hperiod, ih]
  apply Polynomial.eq_of_infinite_eval_eq p (C (p.eval 0))
  apply Set.infinite_of_injective_forall_mem
    (show Function.Injective (fun n : ℕ => (n : K) * c) from by
      intro a b hab
      exact Nat.cast_injective ((mul_right_cancel₀ hc) hab))
  intro n
  simpa only [Set.mem_setOf_eq, eval_C] using hnat n

lemma mem_ideal_shift (c : K) (hc : c ≠ 0) (p : K[X]) :
    p ∈ ideal c ↔ p.eval 0 = 0 ∧ p.eval (c * half) = 0 := by
  simp only [ideal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · rintro ⟨h0, hh⟩
    obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr h0 : (X - C (0 : K)) ∣ p)
    simp only [C_0, sub_zero] at hq
    have hhalf : c * (half : K) ≠ 0 :=
      mul_ne_zero hc (by
        simpa only [half, map_zero] using (algebraMap ℚ K).injective.ne (by norm_num : (1 / 2 : ℚ) ≠ 0))
    have hqh : q.eval (c * half) = 0 := by
      rw [hq, eval_mul, eval_X] at hh
      exact (mul_eq_zero.mp hh).resolve_left hhalf
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqh : (X - C (c * half : K)) ∣ q)
    refine ⟨r, ?_⟩
    rw [hq, hr]
    ring

/-- Rescaling criterion still quantifies over all K-polynomial preimages. -/
theorem monomial_shift_iff (c : K) (hc : c ≠ 0) (n : ℕ) :
    (X : K[X]) ^ n ∈ image c ↔ (LNEDPilot.H n).eval (1 / 2 : ℚ) = 0 := by
  have heval := scaled_half c hc n
  have hnz : c ^ n ≠ 0 := pow_ne_zero n hc
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨h0, hh⟩ := (mem_ideal_shift c hc p).mp hp
    have hk0 : diff c (p - scaledNormalized c n) = 0 := by
      rw [diff_sub, he, scaled_diff c hc, sub_self]
    have hk := kernel_constant_shift c hc (p - scaledNormalized c n) hk0
    have hz : (p - scaledNormalized c n).eval 0 = 0 := by
      rw [eval_sub, h0, scaled_zero, sub_self]
    rw [hz, C_0] at hk
    have heq := sub_eq_zero.mp hk
    have hn : (scaledNormalized c n).eval (c * half) = 0 := by rw [← heq]; exact hh
    rw [heval] at hn
    have hrat := (mul_eq_zero.mp hn).resolve_left hnz
    exact (algebraMap ℚ K).injective (by simpa using hrat)
  · intro hh
    refine ⟨scaledNormalized c n,
      (mem_ideal_shift c hc _).mpr ⟨scaled_zero c n, ?_⟩, scaled_diff c hc n⟩
    rw [heval, hh, map_zero, mul_zero]

lemma even_shift (c : K) (hc : c ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    (X ^ 2 : K[X]) ^ m ∈ image c := by
  have hh := (monomial_image_iff (R := K) (2 * m)).mp
    (by simpa only [pow_mul] using even_image (R := K) m hm)
  simpa only [pow_mul] using (monomial_shift_iff c hc (2 * m)).mpr hh

lemma odd_shift (c : K) (hc : c ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    (X : K[X]) * (X ^ 2 : K[X]) ^ m ∉ image c := by
  intro hv
  have hpow : (X : K[X]) * (X ^ 2 : K[X]) ^ m = X ^ (2 * m + 1) := by
    rw [pow_succ (X : K[X]) (2 * m), pow_mul]
    ring
  apply odd_not_image (R := K) m hm
  rw [hpow] at hv ⊢
  exact (monomial_image_iff _).mpr ((monomial_shift_iff c hc _).mp hv)

theorem nonzero_shift_endpoint (c : K) (hc : c ≠ 0) : ShiftEndpoint c := by
  refine ⟨locally_nilpotent c, E_identity c, even_shift c hc, odd_shift c hc, ?_⟩
  intro hW
  obtain ⟨N, hN⟩ := hW (X ^ 2) (even_shift c hc) X 1
  exact odd_shift c hc (max N 1) (le_max_right N 1)
    (by simpa only [mul_one] using hN (max N 1) (le_max_left N 1))

lemma half_eq : (half : K) = 1 / 2 := by simp [half, map_div₀]

/-- Zero shift is separate: the image is exactly {0}. -/
theorem zero_shift_image : image (0 : K) = {0} := by
  ext p
  simp only [image, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, _, rfl⟩
    simp [diff, shift]
  · rintro rfl
    exact ⟨0, Ideal.zero_mem _, diff_zero 0⟩

theorem zero_shift_mathieu : Mathieu (image (0 : K)) := by
  rw [zero_shift_image]
  intro a ha b d
  have hz : a = 0 := by simpa using ha 1 (by omega)
  refine ⟨1, ?_⟩
  intro m hm
  simp [hz, Nat.ne_of_gt hm]

theorem zero_shift_endpoint_false : ¬ ShiftEndpoint (0 : K) := by
  intro h
  exact h.2.2.2.2 zero_shift_mathieu

#print axioms nonzero_shift_endpoint
#print axioms zero_shift_mathieu
#print axioms zero_shift_endpoint_false
end LNEDExtension
