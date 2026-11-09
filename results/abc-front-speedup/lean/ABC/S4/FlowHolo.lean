import ABC.S4.Defs
import ABC.S4.FlowHoloAux3
import ABC.S4.FlowHoloAux5

/-! L0a: holomorphic dependence on initial data. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- L0a, L0b: ODE substrate
theorem flow_holo {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {γ : ℝ → Cn n} {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t ∧ γ t ∈ U) :
    ∃ r > 0, ∃ φ : ℝ → Cn n → Cn n,
      (∀ t ∈ Icc 0 T, DifferentiableOn ℂ (φ t) (ball (γ 0) r)) ∧
      ∀ x ∈ ball (γ 0) r, φ 0 x = x ∧
        ∀ t ∈ Icc 0 T, HasDerivWithinAt (φ · x) (F (φ t x)) (Icc 0 T) t ∧ φ t x ∈ U := by
  -- tube around `γ`, flow by Picard–Lindelöf + Grönwall, holomorphy via Euler polygons
  have hγc : ContinuousOn γ (Icc 0 T) := fun t ht => (hγ t ht).1.continuousWithinAt
  obtain ⟨ε, hε, L, hL, M, hM, htube⟩ :=
    FlowHoloAux.exists_tube hU hF hγc (fun t ht => (hγ t ht).2)
  obtain ⟨r, hr, φ, hφ⟩ :=
    FlowHoloAux.exists_flow hF hT (fun t ht => (hγ t ht).1) hε hL hM htube
  refine ⟨r, hr, φ, fun t ht => FlowHoloAux.flow_differentiableOn hF htube hL hM hε hφ ht,
    fun x hx => ⟨(hφ x hx).1, fun t ht => ⟨((hφ x hx).2 t ht).1, (htube t ht).1 ?_⟩⟩⟩
  rw [mem_closedBall]
  linarith [((hφ x hx).2 t ht).2]

end ABC.S4
