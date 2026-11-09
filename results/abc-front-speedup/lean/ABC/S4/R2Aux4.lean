import ABC.S4.R2Aux3

/-! R2 helpers: the fundamental matrix `Xf` of the linearisation at `w = 0`: its ODE, `det = 1`
(Liouville), `X(u + 2π) = X(u) X(2π)`, realness on `[0, 2π]`, and `tr X(2π) = jtr P₁ 0`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

/-- `X(t)ᵢⱼ = (∂φ_t/∂xⱼ)(0)ᵢ`, `i, j ∈ {0, 1}`. -/
def Xf (φ : ℂ → Cn 3 → Cn 3) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => fderiv ℂ (φ t) 0 (Pi.single (Fin.castSucc j) 1) (Fin.castSucc i)

/-- `B = J A`, the linearised Hamiltonian field at `w = 0`. -/
def Bm (H₁ : C2 → ℂ → ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Amat H₁ t 0 1, Amat H₁ t 1 1; -Amat H₁ t 0 0, -Amat H₁ t 1 0]

/-- For a traceless `b`, `adj(x) z` is constant along solutions of `x' = b x`, `z' = b z`. -/
theorem adj_mul_const {D : Set ℂ} (hD : IsOpen D) (hD' : IsPreconnected D)
    {x z b : ℂ → Matrix (Fin 2) (Fin 2) ℂ} (hb : ∀ t ∈ D, b t 1 1 = -b t 0 0)
    (hx : ∀ t ∈ D, ∀ i j, HasDerivAt (fun t => x t i j) ((b t * x t) i j) t)
    (hz : ∀ t ∈ D, ∀ i j, HasDerivAt (fun t => z t i j) ((b t * z t) i j) t)
    {t₀ t : ℂ} (ht₀ : t₀ ∈ D) (ht : t ∈ D) :
    (x t).adjugate * z t = (x t₀).adjugate * z t₀ := by
  have hadj : ∀ t ∈ D, ∀ i k, HasDerivAt (fun t => (x t).adjugate i k)
      (((x t).adjugate * -b t) i k) t := by
    intro t ht i k
    have hb' := hb t ht
    simp only [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases k
    · refine (hx t ht 1 1).congr_deriv ?_
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb']; ring
    · refine (hx t ht 0 1).neg.congr_deriv ?_
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb']; ring
    · refine (hx t ht 1 0).neg.congr_deriv ?_
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb']; ring
    · refine (hx t ht 0 0).congr_deriv ?_
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb']; ring
  have hd : ∀ i j, ∀ t ∈ D, HasDerivAt (fun t => ((x t).adjugate * z t) i j) 0 t := by
    intro i j t ht
    have : HasDerivAt (fun t => ∑ k, (x t).adjugate i k * z t k j)
        (∑ k, (((x t).adjugate * -b t) i k * z t k j + (x t).adjugate i k * (b t * z t) k j)) t :=
      HasDerivAt.fun_sum fun k _ => (hadj t ht i k).mul (hz t ht k j)
    refine this.congr_deriv ?_
    rw [Finset.sum_add_distrib, ← Matrix.mul_apply, ← Matrix.mul_apply]
    simp [Matrix.mul_assoc, Matrix.mul_neg]
  ext i j
  exact hD.is_const_of_deriv_eq_zero hD'
    (fun t ht => (hd i j t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd i j t ht).deriv) ht ht₀

section X

variable {H₁ : C2 → ℂ → ℂ} {ρ s s₀ r₀ : ℝ} {φ : ℂ → Cn 3 → Cn 3}

theorem FlowData.tau0 (fd : FlowData H₁ ρ s s₀ r₀ φ) {t : ℂ} (ht : t ∈ Dom s₀) (j : Fin 2) :
    fderiv ℂ (φ t) 0 (Pi.single (Fin.castSucc j) 1) 2 = 0 := by
  have h0b : (0 : Cn 3) ∈ ball (0 : Cn 3) r₀ := mem_ball_self fd.r₀pos
  have hev : (fun x => φ t x 2) =ᶠ[𝓝 0] fun x => x 2 + t := by
    filter_upwards [isOpen_ball.mem_nhds h0b] with x hx using fd.tau hx ht
  have h1 : HasFDerivAt (fun x => φ t x 2)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).comp (fderiv ℂ (φ t) 0)) 0 :=
    by
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).hasFDerivAt.comp 0
        (fd.slice_diffAt ht h0b).differentiableAt.hasFDerivAt
      exact this
  have h2 : HasFDerivAt (fun x : Cn 3 => x 2 + t)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2) 0 :=
    by
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).hasFDerivAt
        (x := 0) |>.add_const t
      exact this
  have := congrArg (fun L => L (Pi.single (Fin.castSucc j) 1))
    ((h1.congr_of_eventuallyEq hev.symm).unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at this
  rw [this]
  fin_cases j <;> simp

theorem FlowData.X_ode (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {t : ℂ} (ht : t ∈ Dom s₀) (i j : Fin 2) :
    HasDerivAt (fun t => Xf φ t i j) ((Bm H₁ t * Xf φ t) i j) t := by
  have hv := (fd.var hH ht).clm_apply (hasDerivAt_const t (Pi.single (Fin.castSucc j) (1 : ℂ)))
  have hc := hasDerivAt_pi.1 hv (Fin.castSucc i)
  simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero] at hc
  refine hc.congr_deriv ?_
  rw [fd.axis hH h0 ht, fderiv_Fvf_axis hH hρ (Dom_strip fd.s₀le ht) (fd.tau0 ht j)]
  fin_cases i <;> simp [Bm, Xf, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem FlowData.X_zero (fd : FlowData H₁ ρ s s₀ r₀ φ) : Xf φ 0 = 1 := by
  have h0b : (0 : Cn 3) ∈ ball (0 : Cn 3) r₀ := mem_ball_self fd.r₀pos
  have hev : φ 0 =ᶠ[𝓝 0] id := by
    filter_upwards [isOpen_ball.mem_nhds h0b] with x hx using fd.init x hx
  have : fderiv ℂ (φ 0) 0 = ContinuousLinearMap.id ℂ (Cn 3) := by
    rw [hev.fderiv_eq, fderiv_id]
  ext i j
  simp only [Xf, this, ContinuousLinearMap.id_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem FlowData.X_det (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {t : ℂ} (ht : t ∈ Dom s₀) :
    (Xf φ t).det = 1 := by
  have hb : ∀ t ∈ Dom s₀, Bm H₁ t 1 1 = -Bm H₁ t 0 0 := by
    intro t ht
    simp [Bm, Amat_symm hH hρ (Dom_strip fd.s₀le ht) 1 0]
  have hode := fun t ht i j => fd.X_ode hH hρ h0 (t := t) ht i j
  have := adj_mul_const (isOpen_Dom s₀) (convex_Dom s₀).isPreconnected hb hode hode
    fd.zero_mem ht
  rw [Matrix.adjugate_mul, Matrix.adjugate_mul, fd.X_zero, Matrix.det_one] at this
  have := congrFun (congrFun this 0) 0
  simpa using this

theorem FlowData.X_per (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {u : ℂ} (hu : u ∈ Dom s₀)
    (hu' : u + 2 * π ∈ Dom s₀) : Xf φ (u + 2 * π) = Xf φ u * Xf φ (2 * π) := by
  set D₁ := Dom s₀ ∩ (fun u => u + 2 * π) ⁻¹' Dom s₀
  have hD₁ : IsOpen D₁ := (isOpen_Dom s₀).inter ((isOpen_Dom s₀).preimage (by fun_prop))
  have hD₁c : Convex ℝ D₁ := by
    refine (convex_Dom s₀).inter ?_
    have : (fun u : ℂ => u + 2 * π) ⁻¹' Dom s₀ = (fun u => (-(2 * π : ℂ)) + u) '' Dom s₀ := by
      ext v; simp only [mem_preimage, mem_image, neg_add_eq_sub]
      exact ⟨fun h => ⟨_, h, by ring⟩, fun ⟨x, hx, hxv⟩ => by rw [← hxv]; simpa using hx⟩
    rw [this]; exact (convex_Dom s₀).translate _
  have hb : ∀ t ∈ D₁, Bm H₁ t 1 1 = -Bm H₁ t 0 0 := by
    intro t ht
    simp [Bm, Amat_symm hH hρ (Dom_strip fd.s₀le ht.1) 1 0]
  have hx := fun t (ht : t ∈ D₁) i j => fd.X_ode hH hρ h0 ht.1 i j
  have hz : ∀ t ∈ D₁, ∀ i j, HasDerivAt (fun t => Xf φ (t + 2 * π) i j)
      ((Bm H₁ t * Xf φ (t + 2 * π)) i j) t := by
    intro t ht i j
    have := (fd.X_ode hH hρ h0 ht.2 i j).comp_add_const t (2 * π)
    simpa [Bm, Amat_per hH] using this
  have h0D : (0 : ℂ) ∈ D₁ := ⟨fd.zero_mem, by
    simpa using real_mem_Dom fd.s₀pos (t := 2 * π) ⟨by positivity, le_rfl⟩⟩
  have := adj_mul_const hD₁ hD₁c.isPreconnected hb hx hz h0D ⟨hu, hu'⟩
  rw [fd.X_zero, Matrix.adjugate_one, Matrix.one_mul, zero_add] at this
  have hdet := fd.X_det hH hρ h0 hu
  calc Xf φ (u + 2 * π) = (Xf φ u * (Xf φ u).adjugate) * Xf φ (u + 2 * π) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
    _ = Xf φ u * Xf φ (2 * π) := by rw [Matrix.mul_assoc, this]

end X

end ABC.S4.R2Aux
