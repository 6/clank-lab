import P16c.MoreIdentities
import P16c.Entries
import P16c.Independence
import P16c.Quadratic
import P16c.Cubic
import P16c.Parameters
import P16c.PolynomialIdentities

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo

lemma t_square (a b : K) : T a b ^ 2 = (a + b) • T a b + 1 := by
  have h := t_quadratic a b
  rw [add_assoc] at h
  simpa using eq_neg_of_add_eq_zero_left h
lemma t₂_square (a b : K) : T₂ a b ^ 2 = (a + b) • T₂ a b + 1 := by
  have h := t₂_quadratic a b
  rw [add_assoc] at h
  simpa using eq_neg_of_add_eq_zero_left h

lemma parameter_tau (l m : K) (hσ : traceParam l ≠ 0) (hτ : traceParam m ≠ 0) :
    (aParam l m + bParam l m) ^ 2 / aParam l m = traceParam m := by
  have hsum : aParam l m + bParam l m = traceParam l := by simp [bParam, add_comm]
  rw [hsum]
  dsimp [aParam]
  field_simp

/-- L3, facet translation. -/
theorem t_order (a b l : K) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hσ : a + b = traceParam l) : orderOf (T a b) = orderOf l := by
  apply quadratic_order _ l hl hl2
  · simpa [hσ, traceParam] using t_square a b
  · exact t_not_scalar a b

lemma t₂_order (a b l : K) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hσ : a + b = traceParam l) : orderOf (T₂ a b) = orderOf l := by
  apply quadratic_order _ l hl hl2
  · simpa [hσ, traceParam] using t₂_square a b
  · exact t₂_not_scalar a b

/-- The split cubic in L3 agrees with the directly checked matrix identity. -/
lemma v_split_cubic (a b m : K) (ha : a ≠ 0) (hm : m ≠ 0)
    (hτ : (a + b) ^ 2 / a = traceParam m) :
    Polynomial.aeval (V a b)
      ((Polynomial.X - Polynomial.C (1 : K)) *
        ((Polynomial.X - Polynomial.C m) * (Polynomial.X - Polynomial.C m⁻¹))) = 0 := by
  rw [map_mul, eval_split_quadratic (V a b) m hm]
  simpa [hτ] using v_cubic a b ha

/-- L3, vertex translation. -/
theorem v_order (a b m : K) (ha : a ≠ 0) (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1)
    (hτ : (a + b) ^ 2 / a = traceParam m) : orderOf (V a b) = orderOf m := by
  apply cubic_order _ m hm (fun h => hm2 (by simp [h])) hm2
    (v_split_cubic a b m ha hm hτ) (v_ne_one a b)

/-- Both exact translation orders with the parameters in the question. -/
theorem translation_orders (s u : ℕ) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    orderOf (T (aParam l m) (bParam l m)) = s ∧
      orderOf (V (aParam l m) (bParam l m)) = u := by
  obtain ⟨hσ, hτ, ha, _, hab⟩ := parameters s u hs3 hu3 hsu l m hl hm
  exact ⟨(t_order _ _ l (nonzero_of_order_ge_three hl hs3)
      (sq_ne_one_of_order_ge_three hl hs3) hab).trans hl,
    (v_order _ _ m ha (nonzero_of_order_ge_three hm hu3)
      (sq_ne_one_of_order_ge_three hm hu3) (parameter_tau l m hσ hτ)).trans hm⟩
end P16c
