import ABC.S4.Defs

/-! R5: frequencies as parameters. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem R5_identity (ν b : ℝ) (hb : b ≠ 0) (R : C2 → ℂ → ℂ) (x : Pt 2)
    (hω : x.2.2 1 ≠ 0) :
    ham (eNP ν b) (pertP ν b R) x =
      x.2.2 1 * (x.1 1 + Kbnf ν b R (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)) (x.2.1 1)) := by
  have hsq : ∀ P θ : ℂ, polarW P θ 0 ^ 2 + polarW P θ 1 ^ 2 = 2 * P := by
    intro P θ
    have h2 : ((2 * P) ^ (1 / 2 : ℂ)) ^ 2 = 2 * P := by simp
    simp only [polarW, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcs := Complex.cos_sq_add_sin_sq θ
    linear_combination ((2 * P) ^ (1 / 2 : ℂ)) ^ 2 * hcs + h2
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hp : 2 * (b : ℂ) * p0 ν b x.2.2 = x.2.2 0 / x.2.2 1 - ν := by
    unfold p0; field_simp
  have hp' : 2 * (b : ℂ) * p0 ν b x.2.2 * x.2.2 1 = x.2.2 0 - ν * x.2.2 1 := by
    rw [hp]; field_simp
  have hK := hsq (p0 ν b x.2.2 + x.1 0) (x.2.1 0)
  simp only [ham, eNP, pertP, Kbnf, Fin.sum_univ_two]
  linear_combination (-(x.2.2 1) * (ν / 2 + b / 4 * ((polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0) 0 ^ 2 +
      polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0) 1 ^ 2) + 2 * (p0 ν b x.2.2 + x.1 0)))) * hK
    - x.1 0 * hp'

end ABC.S4
