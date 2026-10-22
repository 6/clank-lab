import Mathlib

/-!
# Extraction: fifth powers are injective on `1 + tℚ⟦t⟧`

With BLMMR Prop. 2.2 (cited, not formalized), D₅'s ray-(2,1) function is `E⁵` for
`E = 1 + Σ_j τ^{1,5}(2j,j) t^j`; together with `ray21_eq_S5` (`= S⁵`) this gives `E = S`.
-/

namespace ErsConj13

theorem pow5_injective {a b : PowerSeries ℚ} (ha : PowerSeries.constantCoeff a = 1)
    (hb : PowerSeries.constantCoeff b = 1) (h : a ^ 5 = b ^ 5) : a = b := by
  have e : a ^ 5 - b ^ 5 = (a - b) * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) := by
    ring
  have hne : (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [ha, hb] at this
    norm_num at this
  have : (a - b) * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) = 0 := by
    rw [← e, h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)

end ErsConj13
