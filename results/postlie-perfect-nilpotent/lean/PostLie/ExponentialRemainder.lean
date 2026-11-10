import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Rat

namespace PostLie

variable {k V W : Type*} [Field k] [CharZero k]
  [AddCommGroup V] [Module k V] [Module ℚ V]
  [AddCommGroup W] [Module k W] [Module ℚ W]

omit [CharZero k] in
/-- If a linear projection kills the second derivative, its projected exponential is affine. -/
lemma projected_exp_eq (D : Module.End k V) (hD : IsNilpotent D)
    (F : V →ₗ[k] W) (hF : F.comp (D ^ 2) = 0) (v : V) :
    F (IsNilpotent.exp D v) = F v + F (D v) := by
  obtain ⟨r, hr⟩ := hD
  have hr' : D ^ (r + 2) = 0 := pow_eq_zero_of_le (by omega) hr
  have hp (j : ℕ) : F ((D ^ (j + 2)) v) = 0 := by
    rw [Nat.add_comm j 2, pow_add, Module.End.mul_apply]
    exact LinearMap.congr_fun hF ((D ^ j) v)
  rw [IsNilpotent.exp_eq_sum hr', Finset.sum_range_succ', Finset.sum_range_succ']
  simp [map_rat_smul, add_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [show 1 + (j + 1) = j + 2 by omega, hp, smul_zero]

end PostLie
