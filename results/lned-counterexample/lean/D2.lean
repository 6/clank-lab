import D0

namespace LNEDPilot
open Polynomial

noncomputable def H (n : ℕ) : ℚ[X] :=
  C (-(1 / ((n : ℚ) + 1))) *
    (Polynomial.bernoulli (n + 1) - C ((Polynomial.bernoulli (n + 1)).eval 0))

lemma H_zero (n : ℕ) : (H n).eval 0 = 0 := by
  simp [H]

lemma delta_H (n : ℕ) : delta (H n) = (X : ℚ[X]) ^ n := by
  apply Polynomial.funext
  intro q
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hb := Polynomial.bernoulli_eval_one_add (n + 1) q
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hb
  rw [add_comm 1 q] at hb
  simp only [delta, phi, H, eval_sub, eval_mul, eval_C, eval_comp,
    eval_add, eval_X, eval_one, eval_pow]
  rw [hb]
  field_simp [hn]
  <;> ring

#print axioms delta_H
end LNEDPilot
