import ABC.S4.Defs
import ABC.S4.TwistConjAux5

/-! T1: twist invariance. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- T1–T4: twist algebra
theorem twist_conj {f₁ f₂ h : E 2 → E 2} {p : E 2} (hh : ContDiffAt ℝ 3 h p)
    (hh' : (fderiv ℝ h p).ker = ⊥) (hf : ContDiffAt ℝ 3 f₁ p)
    (hdet : jdet f₁ p = 1)
    (hc : ∀ᶠ x in 𝓝 p, f₂ (h x) = h (f₁ x)) : TwistNonzero f₁ p → TwistNonzero f₂ (h p) := by
  rintro ⟨v, a, hd, hβ⟩
  obtain ⟨v₂, b, hd₂, hβ₂⟩ := TwistConjAux.conj_core hh hh' hf hdet hc hd
  exact ⟨v₂, b, hd₂, hβ₂ ▸ hβ⟩

theorem twist_indep {f : E 2 → E 2} {p : E 2} {v : C2} {a : ℕ → ℕ → ℂ}
    (hdet : jdet f p = 1) (ht : TwistNonzero f p)
    (hd : TwistData f p v a) : birkhoffBeta a ≠ 0 := by
  obtain ⟨v', a', hd', hβ'⟩ := ht
  exact TwistConjAux.indep_core hdet hd' hβ' hd

end ABC.S4
