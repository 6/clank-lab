import ABC.S4.TwistConj
import ABC.S4.R123
import ABC.S4.TwistPhiAux2

/-! T2: the twist of `P` and of `Φ ∘ P ∘ Φ⁻¹`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem twist_phi_iff {p : E 2} (hp : CertFacts p) : TwistNonzero retMap p ↔ TwistNonzeroPhi p := by
  obtain ⟨hfix, hret, hdet⟩ := TwistPhiAux.retMap_facts hp
  -- `Φ` is a local diffeomorphism at `p`: its Jacobian is `sin p₁ + cos p₀ ≥ 1.92`
  have hJ : Real.sin (p 1) + Real.cos (p 0) ≠ 0 := by
    linarith [TwistPhiAux.phi_jac_pos hp]
  have hinj := TwistPhiAux.fderiv_phi_injective hJ
  set e : E 2 ≃L[ℝ] E 2 :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ phi p : E 2 →ₗ[ℝ] E 2) hinj).toContinuousLinearEquiv
  have he : (e : E 2 →L[ℝ] E 2) = fderiv ℝ phi p := by ext u; rfl
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hphi3 : ContDiffAt ℝ 3 phi p := TwistPhiAux.phi_contDiff.contDiffAt.of_le le_top
  have hstrict : HasStrictFDerivAt phi (e : E 2 →L[ℝ] E 2) p := by
    rw [he]; exact hphi3.hasStrictFDerivAt hn
  have hker : (fderiv ℝ phi p).ker = ⊥ := LinearMap.ker_eq_bot.2 hinj
  constructor
  · -- (→) conjugate by `h = Φ`; only `ψ ∘ Φ = id` near `p` is used
    intro ht ψ _ hleft
    refine twist_conj hphi3 hker hret hdet ?_ ht
    filter_upwards [hleft] with x hx
    simp [hx]
  · -- (←) conjugate back by the local inverse `ψ` of `Φ`
    intro hphi
    set ψ := hphi3.localInverse hstrict.hasFDerivAt hn
    have hψ : ψ = hstrict.localInverse phi e p := rfl
    have hψ3 : ContDiffAt ℝ 3 ψ (phi p) := hphi3.to_localInverse hstrict.hasFDerivAt hn
    have hψp : ψ (phi p) = p := by rw [hψ]; exact hstrict.localInverse_apply_image
    have hψD : HasFDerivAt ψ (e.symm : E 2 →L[ℝ] E 2) (phi p) := by
      rw [hψ]; exact hstrict.to_localInverse.hasFDerivAt
    have hr : ∀ᶠ X in 𝓝 (phi p), phi (ψ X) = X := by
      rw [hψ]; exact hstrict.eventually_right_inverse
    have hl : ∀ᶠ x in 𝓝 p, ψ (phi x) = x := by
      rw [hψ]; exact hstrict.eventually_left_inverse
    have ht := hphi ψ hr hl
    have hret' : ContDiffAt ℝ 3 retMap (ψ (phi p)) := by rwa [hψp]
    have hphi' : ContDiffAt ℝ 3 phi (retMap (ψ (phi p))) := by rwa [hψp, hfix]
    have hf₁ : ContDiffAt ℝ 3 (phi ∘ retMap ∘ ψ) (phi p) := hphi'.comp (phi p) (hret'.comp (phi p) hψ3)
    have hdet₁ : jdet (phi ∘ retMap ∘ ψ) (phi p) = 1 := by
      unfold jdet
      rw [fderiv_comp (phi p) (hphi'.differentiableAt hn)
          ((hret'.comp (phi p) hψ3).differentiableAt hn),
        fderiv_comp (phi p) (hret'.differentiableAt hn) (hψ3.differentiableAt hn),
        Function.comp_apply,
        hψp, hfix, hψD.fderiv, ← he, TwistPhiAux.det_sandwich _ _ _ (by ext u; simp)]
      exact hdet
    have hker' : (fderiv ℝ ψ (phi p)).ker = ⊥ := by
      rw [hψD.fderiv]; exact LinearMap.ker_eq_bot.2 e.symm.injective
    have hc : ∀ᶠ X in 𝓝 (phi p), retMap (ψ X) = ψ ((phi ∘ retMap ∘ ψ) X) := by
      have htend : Tendsto (retMap ∘ ψ) (𝓝 (phi p)) (𝓝 p) := by
        have h1 : ContinuousAt (retMap ∘ ψ) (phi p) :=
          hret'.continuousAt.comp hψ3.continuousAt
        have h2 : (retMap ∘ ψ) (phi p) = p := by simp [hψp, hfix]
        simpa only [ContinuousAt, h2] using h1
      filter_upwards [htend.eventually hl] with X hX
      exact hX.symm
    have := twist_conj hψ3 hker' hf₁ hdet₁ hc ht
    rwa [hψp] at this

end ABC.S4
