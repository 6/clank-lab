import Mathlib

/-!
# Reflection length as checker A computes it

`ℓ(w) = rank(w - 1)` (checker A's `ell`) on invertible matrices over a field is subadditive,
invariant under conjugation, and zero only at `1`: the hypotheses of Step 2.
-/

namespace RS16

variable {K : Type*} [Field K] {n : ℕ}

/-- `ℓ(w) = rank(w - 1)` -/
noncomputable def rankLen (g : (Matrix (Fin n) (Fin n) K)ˣ) : ℕ :=
  ((g : Matrix (Fin n) (Fin n) K) - 1).rank

lemma matrix_rank_add_le (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

lemma rankLen_mul (x y : (Matrix (Fin n) (Fin n) K)ˣ) :
    rankLen (x * y) ≤ rankLen x + rankLen y := by
  unfold rankLen
  have : ((x * y : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) - 1 =
      (x : Matrix (Fin n) (Fin n) K) * ((y : Matrix (Fin n) (Fin n) K) - 1) +
        ((x : Matrix (Fin n) (Fin n) K) - 1) := by
    rw [Units.val_mul, mul_sub, mul_one]; abel
  rw [this]
  calc _ ≤ ((x : Matrix (Fin n) (Fin n) K) * ((y : Matrix (Fin n) (Fin n) K) - 1)).rank +
        ((x : Matrix (Fin n) (Fin n) K) - 1).rank := matrix_rank_add_le _ _
    _ ≤ ((y : Matrix (Fin n) (Fin n) K) - 1).rank + ((x : Matrix (Fin n) (Fin n) K) - 1).rank :=
        Nat.add_le_add_right (Matrix.rank_mul_le_right _ _) _
    _ = _ := Nat.add_comm _ _

lemma rankLen_conj (g x : (Matrix (Fin n) (Fin n) K)ˣ) : rankLen (g * x * g⁻¹) = rankLen x := by
  unfold rankLen
  have : ((g * x * g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) - 1 =
      (g : Matrix (Fin n) (Fin n) K) * ((x : Matrix (Fin n) (Fin n) K) - 1) *
        ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
  rw [this, Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
  · exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  · exact (Matrix.isUnit_iff_isUnit_det _).mp g⁻¹.isUnit

lemma rankLen_eq_zero (x : (Matrix (Fin n) (Fin n) K)ˣ) : rankLen x = 0 ↔ x = 1 := by
  unfold rankLen Matrix.rank
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  constructor
  · intro h
    have h2 : (x : Matrix (Fin n) (Fin n) K) - 1 = 0 := by
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact h
    exact Units.ext (sub_eq_zero.mp h2)
  · rintro rfl
    simp

end RS16
