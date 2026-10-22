import P16c.Cubic

namespace P16c
open Polynomial
variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- A nonzero vector on which a split quadratic vanishes detects the root period. -/
lemma quadratic_action_period (M W : A) (l : K) (n : ℕ) (hW : W ≠ 0)
    (hq : aeval M ((X - C l) * (X - C l⁻¹)) * W = 0)
    (hn : (M ^ n - 1) * W = 0) : orderOf l ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one]
  by_contra h
  let f : K[X] := X ^ n - 1
  have hinv : (l⁻¹) ^ n ≠ 1 := by simpa [inv_pow] using h
  have hc : IsCoprime ((X - C l) * (X - C l⁻¹)) f :=
    (coprime_linear_of_eval_ne l f (by simpa [f] using sub_ne_zero.mpr h)).mul_left
      (coprime_linear_of_eval_ne l⁻¹ f (by simpa [f] using sub_ne_zero.mpr hinv))
  have hq' : aeval M (X - C l) * (aeval M (X - C l⁻¹) * W) = 0 := by
    simpa [map_mul, mul_assoc] using hq
  obtain ⟨p, q, hpq⟩ := hc
  have hh := congrArg (fun f : K[X] => aeval M f * W) hpq
  have hf : aeval M f * W = 0 := by simpa [f] using hn
  simp only [map_add, map_mul, map_one, add_mul, mul_assoc, hq', hf, mul_zero,
    add_zero, one_mul] at hh
  exact hW hh.symm
end P16c
