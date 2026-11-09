import ABC.S4.PeriodMap
import ABC.S4.R2Aux9

/-! R2: Floquet reduction. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- R2
theorem R2_floquet {H₁ : C2 → ℂ → ℂ} {ρ s : ℝ} {P₁ : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hH : IsTPHam H₁ ρ s)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hP : IsPeriodMap H₁ P₁ ρ)
    (hell : |jtr P₁ 0| < 2) :
    ∃ (ρ' s' ν C : ℝ) (Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (H₂ : C2 → ℂ → ℂ),
      0 < ρ' ∧ 0 < s' ∧ IsTPHam H₂ ρ' s' ∧
      Bound (fun w t => H₂ w t - ν / 2 * (w 0 ^ 2 + w 1 ^ 2)) ρ' s' C 3 ∧
      DifferentiableOn ℂ Q (strip s') ∧ (∀ t, Q (t + 2 * π) = Q t) ∧ (∀ t, (Q t).det = 1) ∧
      (∀ i j, ((Q 0) i j).im = 0) ∧
      Real.cos (2 * π * ν) = jtr P₁ 0 / 2 ∧
      ∀ γ a b, Solves H₂ γ a b → (∀ t ∈ Icc a b, γ t ∈ polydisc ρ') →
        Solves H₁ (fun t => (Q t).mulVec (γ t)) a b := by
  classical
  obtain ⟨s₀, r₀, φ, fd⟩ := R2Aux.flow_exists hρ hs hH h0
  have hT : (2 * π : ℝ) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  have hT' : (2 * π : ℂ) ∈ R2Aux.Dom s₀ := by simpa using R2Aux.real_mem_Dom fd.s₀pos hT
  have hre : ∀ i j, (R2Aux.Xf φ (2 * π) i j).im = 0 := by
    intro i j
    have := fd.X_real hH hρ hs h0 hT i j
    push_cast at this; exact this
  have hdet := fd.X_det hH hρ h0 hT'
  have hjtr := fd.X_jtr hH hρ hs h0 hP
  obtain ⟨S, ν, hNF, hcos⟩ := R2Aux.exists_NF hre hdet (by rw [← hjtr]; exact hell)
  set Q := R2Aux.Qf φ S ν s₀ with hQ
  obtain ⟨Kq, hKq0, hKq⟩ := fd.Qf_bound hH hρ h0 hNF
  have hq : R2Aux.QData H₁ s s₀ ν Kq Q :=
    { s₀pos := fd.s₀pos, s₀le := fd.s₀le, Kq0 := hKq0, holo := fd.Qf_holo hH hρ h0 hNF,
      per := fun t => R2Aux.Qf_per t, det := fd.Qf_det hH hρ h0 hNF,
      real := fd.Qf_real hH hρ hs h0 hNF, bound := hKq,
      ode := fun t ht i j => fd.Qf_ode hH hρ h0 hNF ht i j }
  obtain ⟨C, hC⟩ := R2Aux.remH_bound hH hρ h0 hq
  have hρ₁ := R2Aux.rad_pos hρ hKq0
  have hs₀ := fd.s₀pos
  have hsub : polydisc (R2Aux.rad ρ Kq) ×ˢ strip (s₀ / 2) ⊆ R2Aux.Wset ρ Kq s₀ := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    refine ⟨?_, ?_⟩
    · show ‖w‖ < 2 * R2Aux.rad ρ Kq; have : ‖w‖ < R2Aux.rad ρ Kq := hw; linarith
    · show |t.im| < 3 * s₀ / 4; have : |t.im| < s₀ / 2 := ht; linarith
  refine ⟨R2Aux.rad ρ Kq, s₀ / 2, ν, C, Q, R2Aux.H2 H₁ Q ν, hρ₁, by positivity, ⟨?_, ?_, ?_⟩,
    ?_, ?_, fun t => R2Aux.Qf_per t, fd.Qf_det hH hρ h0 hNF, ?_, ?_, ?_⟩
  · -- holomorphy of `H₂`
    have hp : DifferentiableOn ℂ (fun q : C2 × ℂ => (ν : ℂ) / 2 * (q.1 0 ^ 2 + q.1 1 ^ 2))
        (polydisc (R2Aux.rad ρ Kq) ×ˢ strip (s₀ / 2)) :=
      (by fun_prop : Differentiable ℂ fun q : C2 × ℂ => (ν : ℂ) / 2 * (q.1 0 ^ 2 + q.1 1 ^ 2)).differentiableOn
    exact hp.add ((R2Aux.remH_holo hH hρ hq).mono hsub)
  · -- realness
    intro x t hx
    have h := R2Aux.remH_real hH hρ hs hq (x := x) (by linarith) t
    simp only [R2Aux.H2, Complex.add_im, h, add_zero]
    simp [ofR, Complex.mul_im, Complex.div_ofNat_im, Complex.div_ofNat_re, pow_two]
  · -- periodicity
    intro w t
    simp only [R2Aux.H2, R2Aux.remH_per hH hq]
  · -- the cubic remainder bound
    intro w hw t ht
    have := hC w hw t ht
    simpa [R2Aux.H2] using this
  · -- holomorphy of `Q`
    have : DifferentiableOn ℂ (fun t => (fun i j => Q t i j : Fin 2 → Fin 2 → ℂ)) (strip (s₀ / 2)) :=
      differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j =>
        (hq.holo i j).mono fun t ht => by
          show |t.im| < s₀; have : |t.im| < s₀ / 2 := ht; linarith
    exact this
  · -- `Q(0) = S` is real
    intro i j
    rw [hQ, fd.Qf_zero]; exact hNF.real i j
  · rw [hcos, hjtr]
  · intro γ a b hγ hmem
    exact R2Aux.solves_transfer hH hρ hq hγ hmem

end ABC.S4
