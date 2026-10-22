import P16c.Translations
import P16c.QuadraticAction

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo

/-- L4(iii): the fixed-space calculation forces independence of the vertex directions. -/
theorem vertex_power_independence (a b m : K) (ha : a ≠ 0) (hm : m ≠ 0)
    (hm2 : m ^ 2 ≠ 1) (hτ : (a + b) ^ 2 / a = traceParam m) (i j : ℕ)
    (h : V a b ^ i * V₂ a b ^ j = 1) : orderOf m ∣ i ∧ orderOf m ∣ j := by
  let W : Mat K := V a b ^ 2 + ((a + b) ^ 2 / a) • V a b + 1
  have hW : W ≠ 0 := by
    intro hz
    have he := v_quadratic_entry a b ha
    change W 0 0 = _ at he
    rw [hz] at he
    have htrace := traceParam_ne_zero hm hm2
    rw [hτ] at he
    exact htrace he.symm
  have hfixed : V a b * W = W := by
    have hh := v_cubic a b ha
    change (V a b + 1) * W = 0 at hh
    rw [add_mul, one_mul] at hh
    simpa using eq_neg_of_add_eq_zero_left hh
  have hfixedpow : ∀ n : ℕ, V a b ^ n * W = W := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, ih, hfixed]
  have hjW : V₂ a b ^ j * W = W := by
    calc
      V₂ a b ^ j * W = V₂ a b ^ j * (V a b ^ i * W) := by rw [hfixedpow]
      _ = (V a b ^ i * V₂ a b ^ j) * W := by
        rw [← mul_assoc, ((show Commute (V a b) (V₂ a b) from v_commute a b ha).pow_pow i j).eq]
      _ = W := by rw [h, one_mul]
  have hj : orderOf m ∣ j := by
    apply quadratic_action_period (V₂ a b) W m j hW
    · rw [eval_split_quadratic (V₂ a b) m hm, ← hτ]
      exact v₂_on_fixed a b ha
    · rw [sub_mul, hjW, one_mul, sub_self]
  have hv₂order : orderOf (V₂ a b) = orderOf (V a b) := by
    apply orderOf_eq_orderOf_iff.mpr
    intro n
    have hr : r b * r b = 1 := by simpa [pow_two] using r_sq b
    have hconj : ∀ n : ℕ, V₂ a b ^ n = r b * V a b ^ n * r b := by
      intro n
      induction n with
      | zero => simpa using hr.symm
      | succ n ih =>
        rw [pow_succ, ih, V₂]
        simp only [mul_assoc]
        rw [← mul_assoc (r b) (r b), hr, one_mul]
        simp only [pow_succ, mul_assoc]
    rw [hconj]
    constructor
    · intro hn
      have hh := congrArg (fun X : Mat K => r b * X * r b) hn
      simpa [mul_assoc, ← mul_assoc (r b) (r b), hr] using hh
    · intro hn
      simpa [hn] using hr
  have hv₂j : V₂ a b ^ j = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [hv₂order, v_order a b m ha hm hm2 hτ] using hj
  have hi : V a b ^ i = 1 := by simpa [hv₂j] using h
  refine ⟨?_, hj⟩
  rw [← v_order a b m ha hm hm2 hτ]
  exact orderOf_dvd_of_pow_eq_one hi
end P16c
