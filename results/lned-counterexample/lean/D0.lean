import HardUnit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Span

namespace LNEDPilot
open Polynomial

noncomputable def phiAlg : ℚ[X] →ₐ[ℚ] ℚ[X] where
  toFun := phi
  map_zero' := by simp [phi]
  map_one' := by simp [phi]
  map_add' h k := by simp [phi, add_comp]
  map_mul' h k := by simp [phi, mul_comp]
  commutes' a := by simp [phi, C_comp]

lemma delta_zero : delta 0 = 0 := by simp [delta, phi]
lemma delta_C (a : ℚ) : delta (C a) = 0 := by simp [delta, phi, C_comp]
lemma delta_add (h k : ℚ[X]) : delta (h + k) = delta h + delta k := by
  simp only [delta, phi, add_comp]
  ring
lemma delta_sub (h k : ℚ[X]) : delta (h - k) = delta h - delta k := by
  simp only [delta, phi, sub_comp]
  ring
lemma delta_smul (a : ℚ) (h : ℚ[X]) : delta (a • h) = a • delta h := by
  have hp : phi (a • h) = a • phi h := by
    simp only [phi, smul_eq_C_mul, mul_comp, C_comp]
  simp only [delta, hp, smul_sub]

noncomputable def deltaLinear : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := delta
  map_add' := delta_add
  map_smul' := delta_smul

lemma delta_E (h k : ℚ[X]) :
    delta (h * k) = delta h * k + h * delta k - delta h * delta k := by
  simp only [delta, phi, mul_comp]
  ring

lemma I_eq_ideal : I = (Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} : Ideal ℚ[X]) := by
  ext h
  simp only [I, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_def]

lemma mem_I_iff (h : ℚ[X]) : h ∈ I ↔ h.eval 0 = 0 ∧ h.eval (1 / 2 : ℚ) = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · rintro ⟨h0, hh⟩
    have hx : (X : ℚ[X]) ∣ h := by
      simpa using (dvd_iff_isRoot.mpr h0 : (X - C (0 : ℚ)) ∣ h)
    obtain ⟨q, hq⟩ := hx
    have hqh : q.eval (1 / 2 : ℚ) = 0 := by
      rw [hq, eval_mul, eval_X] at hh
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqh : (X - C (1 / 2 : ℚ)) ∣ q)
    refine ⟨r, ?_⟩
    rw [hq, hr]
    ring

lemma delta_kernel_constant (h : ℚ[X]) (hd : delta h = 0) :
    h = C (h.eval 0) := by
  have hp : h = phi h := sub_eq_zero.mp hd
  have hperiod (q : ℚ) : h.eval (q + 1) = h.eval q := by
    have hh := congrArg (Polynomial.eval q) hp
    simpa only [phi, eval_comp, eval_add, eval_X, eval_one] using hh.symm
  have hnat : ∀ n : ℕ, h.eval (n : ℚ) = h.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hperiod, ih]
  apply Polynomial.eq_of_infinite_eval_eq h (C (h.eval 0))
  apply Set.infinite_of_injective_forall_mem
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))
  intro n
  simpa only [Set.mem_setOf_eq, eval_C] using hnat n

#print axioms mem_I_iff
#print axioms delta_kernel_constant
end LNEDPilot
