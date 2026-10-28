import FieldClaim

namespace LNEDScope
open Polynomial LNEDExtension
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

/-- The contained-ideal and strong-radical endpoints. -/
def StrongRadical (W : Set K[X]) : Set K[X] :=
  {a | ∀ b : K[X], ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m ∈ W}
def ScopeEndpoint (K : Type*) [Field K] [CharZero K] : Prop :=
  (∀ J : Ideal K[X], (J : Set K[X]) ⊆ image 1 → J = ⊥) ∧
  StrongRadical (image (1 : K)) = {0}

noncomputable def primitive (c : K) (f : K[X]) : K[X] :=
  f.sum fun n a => a • scaledNormalized c n

lemma primitive_add (c : K) (f g : K[X]) :
    primitive c (f + g) = primitive c f + primitive c g := by
  exact Polynomial.sum_add_index f g _ (by simp) (by intros; exact add_smul _ _ _)
lemma primitive_smul (c a : K) (f : K[X]) :
    primitive c (a • f) = a • primitive c f := by
  unfold primitive
  rw [Polynomial.sum_smul_index f a _ (fun n => zero_smul K (scaledNormalized c n)),
    Polynomial.smul_sum]
  simp only [mul_smul]
lemma primitive_zero (c : K) (f : K[X]) : (primitive c f).eval 0 = 0 := by
  simp [primitive, Polynomial.sum_def, eval_finset_sum, scaled_zero]
lemma primitive_diff (c : K) (hc : c ≠ 0) (f : K[X]) :
    diff c (primitive c f) = f := by
  change diffLinear c (f.sum fun n a => a • scaledNormalized c n) = f
  simp only [Polynomial.sum_def, map_sum, map_smul, diffLinear_apply, scaled_diff c hc]
  simpa only [smul_eq_C_mul] using f.sum_C_mul_X_pow_eq

noncomputable def F : K[X] →ₗ[K] K where
  toFun f := -2 * (primitive 1 f).eval (1 / 2 : K)
  map_add' f g := by simp [primitive_add, eval_add]; ring
  map_smul' a f := by simp [primitive_smul, eval_smul, smul_eq_mul]; ring

lemma F_apply (f : K[X]) : F f = -2 * (primitive 1 f).eval (1 / 2 : K) := rfl

lemma mem_image_iff (f : K[X]) : f ∈ image (1 : K) ↔ F f = 0 := by
  have hh : (half : K) = 1 / 2 := half_eq
  have h2 : (-2 : K) ≠ 0 := by norm_num
  have hprim : f ∈ image (1 : K) ↔ (primitive 1 f).eval (1 / 2 : K) = 0 := by
    constructor
    · rintro ⟨g, hg, he⟩
      obtain ⟨hg0, hgh⟩ := (mem_ideal_one g).mp hg
      have hk : diff 1 (g - primitive 1 f) = 0 := by
        rw [diff_sub, he, primitive_diff 1 one_ne_zero, sub_self]
      have hconst := kernel_constant (g - primitive 1 f) hk
      have hz : (g - primitive 1 f).eval 0 = 0 := by
        rw [eval_sub, hg0, primitive_zero, sub_self]
      rw [hz, C_0] at hconst
      have heq := sub_eq_zero.mp hconst
      rw [← heq, ← hh]
      exact hgh
    · intro hp
      exact ⟨primitive 1 f, (mem_ideal_one _).mpr ⟨primitive_zero 1 f, by rwa [hh]⟩,
        primitive_diff 1 one_ne_zero f⟩
  rw [hprim, F_apply, mul_eq_zero]
  simp [h2]

lemma primitive_of_diff (g : K[X]) : primitive 1 (diff 1 g) = g - C (g.eval 0) := by
  have hk : diff 1 (g - primitive 1 (diff 1 g)) = 0 := by
    rw [diff_sub, primitive_diff 1 one_ne_zero, sub_self]
  have h := kernel_constant (g - primitive 1 (diff 1 g)) hk
  simp only [eval_sub, primitive_zero, sub_zero] at h
  apply (eq_sub_iff_add_eq).mpr
  rw [sub_eq_iff_eq_add] at h
  exact (add_comm _ _).trans h.symm

lemma F_diff (g : K[X]) : F (diff 1 g) = 2 * (g.eval 0 - g.eval (1 / 2 : K)) := by
  rw [F_apply, primitive_of_diff]
  simp only [eval_sub, eval_C]
  ring

lemma shift_shift (s t : K) (f : K[X]) : shift s (shift t f) = shift (s + t) f := by
  simp only [shift, comp_assoc]
  congr 1
  simp only [add_comp, X_comp, C_comp, map_add]
  ring
lemma shift_inverse (t : K) (f : K[X]) : shift (-t) (shift t f) = f := by
  rw [shift_shift, neg_add_cancel]
  simp [shift]
lemma shift_sub (s : K) (f g : K[X]) : shift s (f - g) = shift s f - shift s g := by
  simp only [shift, sub_comp]
lemma shift_mul (s : K) (f g : K[X]) : shift s (f * g) = shift s f * shift s g := by
  simp only [shift, mul_comp]
lemma shift_half_twice (f : K[X]) : shift (1 / 2 : K) (shift (1 / 2 : K) f) = shift 1 f := by
  rw [shift_shift]
  congr 1
  norm_num

theorem F_halfshift (f : K[X]) : F (f + shift (1 / 2 : K) f) = 2 * f.eval 0 := by
  let g := primitive (1 / 2 : K) f
  have hg : diff (1 / 2 : K) g = f := primitive_diff _ (by norm_num) f
  have he : f + shift (1 / 2 : K) f = diff 1 g := by
    rw [← hg]
    unfold diff
    rw [shift_sub, shift_half_twice]
    ring
  rw [he, F_diff]
  rw [← hg]
  simp only [diff, shift, eval_sub, eval_comp, eval_add, eval_X, eval_C, zero_add]

theorem F_one : F (1 : K[X]) = 1 := by
  have h := F_halfshift (1 : K[X])
  simp only [shift, one_comp, map_add, eval_one, mul_one] at h
  apply mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0)
  simpa only [two_mul, mul_one] using h

lemma F_C (a : K) : F (C a) = a := by
  have h : (C a : K[X]) = a • 1 := by simp [smul_eq_C_mul]
  rw [h, map_smul, F_one]
  simp

#print axioms mem_image_iff
#print axioms F_halfshift
#print axioms F_one
end LNEDScope
