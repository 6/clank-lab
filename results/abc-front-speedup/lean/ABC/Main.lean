import ABC.TubeProof
import ABC.S4.KAMInput
import ABC.Rescale
import ABC.Hyp
import ABC.Positivity
import ABC.Drift
import ABC.Cited.Zlatos

/-!
# Main theorem: linear KPP front speed-up in the 1-1-1 ABC flow

For `V(x,y,z) = (sin z + cos y, sin x + cos z, sin y + cos x)`, every `f` satisfying Zlatoš's
(1.2) and every unit vector `e`, the minimal speed `c*_e(K)` of `2π`-periodic pulsating fronts of
`T_t + K V·∇T = ΔT + f(T)` satisfies: `lim_{K→∞} c*_e(K)/K` exists and is positive.
-/

open Filter Topology

namespace ABC

theorem abc_kpp_linear_speedup (f : ℝ → ℝ) (hf : ZlatosKPP f) (e : E 3) (he : ‖e‖ = 1) :
    ∃ ℓ : ℝ, 0 < ℓ ∧
      Tendsto (fun K => cstar (2 * Real.pi) abcField f e K / K) atTop (𝓝 ℓ) := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  set g : ℝ → ℝ := fun s => (2 * Real.pi) ^ 2 * f s
  have hg : ZlatosKPP g := zlatosKPP_smul hf (by positivity)
  obtain ⟨W, hW⟩ := vortex_tube_exists S4.kam_input
  obtain ⟨w, C, hwL, hwp, hwi, hβ⟩ := drift_unit hW e he
  refine ⟨zlatosSup abcUnit g e,
    zlatosSup_pos abcUnit g e hg zlatosFlow_abcUnit w C hwL hwp hwi hβ, ?_⟩
  have hZ := Zlatos2010.theorem_1_1 abcUnit g e hg zlatosFlow_abcUnit he
  have hK : Tendsto (fun K : ℝ => 2 * Real.pi * K) atTop atTop :=
    tendsto_id.const_mul_atTop h2π
  refine (hZ.comp hK).congr fun K => ?_
  simp only [Function.comp, cstar_rescale f e K, g]
  rw [div_div, mul_comm (2 * Real.pi) K, mul_comm K]

end ABC
