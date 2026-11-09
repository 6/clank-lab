import ABC.S4.Defs

/-! R1: the z-flow is Hamiltonian in Φ-coordinates. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem R1_hamiltonian (q : C2) (z : ℂ) (hq : Complex.sin (q 1) + Complex.cos (q 0) ≠ 0)
    (ξ : C2) :
    symp (fderiv ℂ phiC q (zField q z)) (fderiv ℂ phiC q ξ) = fderiv ℂ (Hraw · z) q ξ := by
  -- the components of `Φ` and `H` as compositions of coordinate projections
  have h0 : HasFDerivAt (fun w : C2 => phiC w 0) _ q :=
    ((hasFDerivAt_apply (𝕜 := ℂ) 0 q).mul (hasFDerivAt_apply (𝕜 := ℂ) 1 q).csin).add
      (hasFDerivAt_apply (𝕜 := ℂ) 0 q).csin
  have h1 : HasFDerivAt (fun w : C2 => phiC w 1) _ q := hasFDerivAt_apply (𝕜 := ℂ) 1 q
  have hH : HasFDerivAt (Hraw · z) _ q :=
    ((((hasFDerivAt_apply (𝕜 := ℂ) 1 q).mul_const (Complex.sin z)).add
      (hasFDerivAt_apply (𝕜 := ℂ) 1 q).csin).add (hasFDerivAt_apply (𝕜 := ℂ) 0 q).ccos).sub
      ((hasFDerivAt_apply (𝕜 := ℂ) 0 q).mul_const (Complex.cos z))
  have hd : DifferentiableAt ℂ phiC q :=
    differentiableAt_pi.2 fun i => by fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      [exact h0.differentiableAt; exact h1.differentiableAt]
  have hc : ∀ (i : Fin 2) (v : C2),
      fderiv ℂ phiC q v i = fderiv ℂ (fun w : C2 => phiC w i) q v := fun i v => by
    rw [(hasFDerivAt_pi'.1 hd.hasFDerivAt i).fderiv]; rfl
  have e : ∀ v : C2, fderiv ℂ phiC q v 0 =
      (Complex.sin (q 1) + Complex.cos (q 0)) * v 0 + q 0 * Complex.cos (q 1) * v 1 := by
    intro v; rw [hc, h0.fderiv]; simp; ring
  have e1 : ∀ v : C2, fderiv ℂ phiC q v 1 = v 1 := by
    intro v; rw [hc, h1.fderiv]; simp
  rw [hH.fderiv]
  simp only [symp, e, e1, zField]
  simp
  field_simp
  ring

end ABC.S4
