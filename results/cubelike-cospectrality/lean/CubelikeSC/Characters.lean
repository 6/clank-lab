import Mathlib
import CubelikeSC.Statement

/-!
# Characters of `(ZMod 2)^m`

`χ(a, x) = (-1)^{a·x}`; multiplicativity and orthogonality
`Σ_a χ(a, x) = 2^m [x = 0]`.
-/

namespace CubelikeSC

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma neg_one_pow_val_add (x y : ZMod 2) :
    ((-1 : ℤ) ^ (x + y).val) = (-1) ^ x.val * (-1) ^ y.val := by
  fin_cases x <;> fin_cases y <;> decide

lemma neg_one_pow_val_eq (x : ZMod 2) : ((-1 : ℤ) ^ x.val) = 1 - 2 * (x.val : ℤ) := by
  revert x; decide

lemma add_eq_zero_iff_eq' {m : Type*} (x y : m → ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rcases zmod2_cases (x i) with hx | hx <;> rcases zmod2_cases (y i) with hy | hy <;>
      simp_all
  · rintro rfl; funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    rcases zmod2_cases (x i) with hx | hx <;> rw [hx] <;> decide

/-- Orthogonality of the characters of `(ZMod 2)^m`. -/
lemma sum_char {m : ℕ} (x : Fin m → ZMod 2) :
    ∑ a : Fin m → ZMod 2, ((-1 : ℤ) ^ (a ⬝ᵥ x).val) = if x = 0 then 2 ^ m else 0 := by
  split_ifs with hx
  · subst hx; simp [ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    have hxi : x i = 1 := (zmod2_cases (x i)).resolve_left hi
    set e : Fin m → ZMod 2 := Pi.single i 1
    have hshift : ∀ a : Fin m → ZMod 2,
        ((-1 : ℤ) ^ ((a + e) ⬝ᵥ x).val) = -((-1) ^ (a ⬝ᵥ x).val) := by
      intro a
      have : e ⬝ᵥ x = 1 := by simp [e, hxi]
      have h1 : ((-1 : ℤ) ^ (1 : ZMod 2).val) = -1 := by decide
      rw [add_dotProduct, this, neg_one_pow_val_add, h1]
      ring
    have h1 := Fintype.sum_equiv (Equiv.addRight e) (fun a => ((-1 : ℤ) ^ ((a + e) ⬝ᵥ x).val))
      (fun a => ((-1 : ℤ) ^ (a ⬝ᵥ x).val)) (fun a => rfl)
    simp only [hshift, Finset.sum_neg_distrib] at h1
    linarith

end CubelikeSC
