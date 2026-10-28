import ScopeFunctional

namespace LNEDScope
open Polynomial LNEDExtension
variable {K : Type*} [Field K] [CharZero K]

noncomputable def ann : Ideal K[X] where
  carrier := {p | ∀ f : K[X], F (p * f) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq f
    rw [add_mul, map_add, hp f, hq f, add_zero]
  smul_mem' := by
    intro a p hp f
    change F ((a * p) * f) = 0
    convert hp (a * f) using 1 <;> ring

lemma ann_mem (p : K[X]) : p ∈ ann ↔ ∀ f : K[X], F (p * f) = 0 := Iff.rfl

lemma ann_degree_ne_zero (p : K[X]) (hp : p ∈ ann) (hp0 : p ≠ 0) : p.natDegree ≠ 0 := by
  intro hd
  have he := eq_C_of_natDegree_eq_zero hd
  have hf := hp 1
  rw [mul_one, he, F_C] at hf
  exact hp0 (by rw [he, hf, C_0])

lemma diff_ne_zero (c : K) (hc : c ≠ 0) (p : K[X]) (hp : p.natDegree ≠ 0) : diff c p ≠ 0 := by
  intro hz
  have he := kernel_constant_shift c hc p hz
  exact hp (by rw [he, natDegree_C])

lemma ann_Xback (p : K[X]) (hp : p ∈ ann) :
    X * shift (-(1 / 2 : K)) p ∈ ann := by
  intro f
  have hs : shift (1 / 2 : K) (shift (-(1 / 2 : K)) p) = p := by
    simpa only [neg_neg] using shift_inverse (-(1 / 2 : K)) p
  have h := F_halfshift (shift (-(1 / 2 : K)) p * (X * f))
  rw [map_add, shift_mul, hs, hp] at h
  simp only [shift, eval_mul, eval_X, zero_mul, mul_zero, add_zero] at h
  simpa only [shift, mul_assoc, mul_left_comm, mul_comm] using h

lemma ann_shift_of_zero (q : K[X]) (hq : q ∈ ann) (hq0 : q.eval 0 = 0) :
    shift (1 / 2 : K) q ∈ ann := by
  intro f
  have hs : shift (1 / 2 : K) (shift (-(1 / 2 : K)) f) = f := by
    simpa only [neg_neg] using shift_inverse (-(1 / 2 : K)) f
  have h := F_halfshift (q * shift (-(1 / 2 : K)) f)
  rw [map_add, hq, zero_add, shift_mul, hs, eval_mul, hq0, zero_mul, mul_zero] at h
  exact h

theorem annihilator_eq_bot : (ann : Ideal K[X]) = ⊥ := by
  have hall : ∀ n : ℕ, ∀ p : K[X], p.natDegree = n → p ∈ ann → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpn hp
      by_contra hp0
      have hpd := ann_degree_ne_zero p hp hp0
      have hc : (-(1 / 2 : K)) ≠ 0 := by norm_num
      have hdp : diff (-(1 / 2 : K)) p ≠ 0 := diff_ne_zero _ hc p hpd
      let r : K[X] := X * diff (-(1 / 2 : K)) p
      have hr0 : r ≠ 0 := mul_ne_zero X_ne_zero hdp
      have hr : r ∈ ann := by
        have h1 : X * p ∈ ann := (ann : Ideal K[X]).mul_mem_left X hp
        have h2 := ann_Xback p hp
        have hh := (ann : Ideal K[X]).sub_mem h1 h2
        convert hh using 1 <;> simp only [r, diff] <;> ring
      have hreval : r.eval 0 = 0 := by simp [r]
      have hrd : r.natDegree ≠ 0 := ann_degree_ne_zero r hr hr0
      have hrle : r.natDegree ≤ p.natDegree := by
        have hdlt := natDegree_lt_natDegree hdp (diff_degree_lt _ p hp0)
        dsimp [r]
        rw [natDegree_X_mul hdp]
        omega
      have hsr : shift (1 / 2 : K) r ∈ ann := ann_shift_of_zero r hr hreval
      have hdr : diff (1 / 2 : K) r ≠ 0 := diff_ne_zero _ (by norm_num) r hrd
      have hmem : diff (1 / 2 : K) r ∈ ann := (ann : Ideal K[X]).sub_mem hr hsr
      have hdlt : (diff (1 / 2 : K) r).natDegree < n := by
        have hlt := natDegree_lt_natDegree hdr (diff_degree_lt _ r hr0)
        omega
      exact hdr (ih _ hdlt _ rfl hmem)
  apply le_bot_iff.mp
  intro p hp
  exact (Ideal.mem_bot).mpr (hall p.natDegree p rfl hp)

/-- Every contained ideal is literally zero in the actual unit-difference image. -/
theorem no_nonzero_contained_ideal (J : Ideal K[X])
    (hJ : (J : Set K[X]) ⊆ image (1 : K)) : J = ⊥ := by
  have hle : J ≤ ann := by
    intro p hp f
    apply (mem_image_iff _).mp
    apply hJ
    simpa only [mul_comm] using J.mul_mem_left f hp
  rw [annihilator_eq_bot] at hle
  exact le_bot_iff.mp hle

#print axioms annihilator_eq_bot
#print axioms no_nonzero_contained_ideal
end LNEDScope
