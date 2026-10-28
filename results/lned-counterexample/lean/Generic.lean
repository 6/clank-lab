import Statements

namespace LNEDExtension
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R]

noncomputable def normalized (n : ℕ) : R[X] := (LNEDPilot.H n).map (algebraMap ℚ R)

lemma diff_sub (c : R) (p q : R[X]) : diff c (p - q) = diff c p - diff c q := by
  simp only [diff, shift, sub_comp]
  ring

lemma diff_map (p : ℚ[X]) :
    diff (1 : R) (p.map (algebraMap ℚ R)) = (LNEDPilot.delta p).map (algebraMap ℚ R) := by
  simp [diff, shift, LNEDPilot.delta, LNEDPilot.phi, Polynomial.map_comp]

lemma normalized_diff (n : ℕ) : diff (1 : R) (normalized n) = (X : R[X]) ^ n := by
  rw [normalized, diff_map, LNEDPilot.delta_H]
  simp

lemma normalized_eval (n : ℕ) (q : ℚ) :
    (normalized n : R[X]).eval (algebraMap ℚ R q) =
      algebraMap ℚ R ((LNEDPilot.H n).eval q) := by
  rw [normalized, eval_map, eval₂_at_apply]

lemma normalized_zero (n : ℕ) : (normalized n : R[X]).eval 0 = 0 := by
  simpa using (normalized_eval (R := R) n 0).trans (by rw [LNEDPilot.H_zero, map_zero])

lemma kernel_constant (p : R[X]) (hd : diff 1 p = 0) : p = C (p.eval 0) := by
  have hp : p = shift 1 p := sub_eq_zero.mp hd
  have hperiod (q : R) : p.eval (q + 1) = p.eval q := by
    have hh := congrArg (Polynomial.eval q) hp
    simpa only [shift, eval_comp, eval_add, eval_X, eval_C] using hh.symm
  have hnat : ∀ n : ℕ, p.eval (n : R) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hperiod, ih]
  apply Polynomial.eq_of_infinite_eval_eq p (C (p.eval 0))
  apply Set.infinite_of_injective_forall_mem
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : R)))
  intro n
  simpa only [Set.mem_setOf_eq, eval_C] using hnat n

lemma mem_ideal_one (p : R[X]) :
    p ∈ ideal 1 ↔ p.eval 0 = 0 ∧ p.eval half = 0 := by
  simp only [ideal, one_mul, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · rintro ⟨h0, hh⟩
    obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr h0 : (X - C (0 : R)) ∣ p)
    simp only [C_0, sub_zero] at hq
    have hhalf : (half : R) ≠ 0 := by
      simpa only [half, map_zero] using (algebraMap ℚ R).injective.ne (by norm_num : (1 / 2 : ℚ) ≠ 0)
    have hqh : q.eval half = 0 := by
      rw [hq, eval_mul, eval_X] at hh
      exact (mul_eq_zero.mp hh).resolve_left hhalf
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqh : (X - C (half : R)) ∣ q)
    refine ⟨r, ?_⟩
    rw [hq, hr]
    ring

/-- The hard unit quantifies over all R-polynomial preimages. -/
theorem monomial_image_iff (n : ℕ) :
    (X : R[X]) ^ n ∈ image 1 ↔ (LNEDPilot.H n).eval (1 / 2 : ℚ) = 0 := by
  have hinj := (algebraMap ℚ R).injective
  have heval : (normalized n : R[X]).eval half =
      algebraMap ℚ R ((LNEDPilot.H n).eval (1 / 2 : ℚ)) := normalized_eval n (1 / 2)
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨h0, hh⟩ := (mem_ideal_one p).mp hp
    have hk0 : diff 1 (p - normalized n) = 0 := by
      rw [diff_sub, he, normalized_diff, sub_self]
    have hk := kernel_constant (p - normalized n) hk0
    have hc : (p - normalized n).eval 0 = 0 := by
      rw [eval_sub, h0, normalized_zero, sub_self]
    rw [hc, C_0] at hk
    have heq := sub_eq_zero.mp hk
    have hn : (normalized n : R[X]).eval half = 0 := by rw [← heq]; exact hh
    rw [heval] at hn
    exact hinj (by simpa using hn)
  · intro hh
    refine ⟨normalized n, (mem_ideal_one _).mpr ⟨normalized_zero n, ?_⟩, normalized_diff n⟩
    rw [heval, hh, map_zero]

#print axioms monomial_image_iff
end LNEDExtension
