import ABC.S4.TwistPhiAux1

/-! T2 helper: `retMap` is smooth and area-preserving at `p` (via R1), and `Φ` is a local
diffeomorphism at `p`. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.TwistPhiAux

/-- `det (A ∘ D ∘ B) = det D` when `B ∘ A = id`. -/
theorem det_sandwich (A D B : E 2 →L[ℝ] E 2) (hBA : B.comp A = ContinuousLinearMap.id ℝ (E 2)) :
    LinearMap.det ((A.comp (D.comp B) : E 2 →L[ℝ] E 2) : E 2 →ₗ[ℝ] E 2) =
      LinearMap.det (D : E 2 →ₗ[ℝ] E 2) := by
  have h1 : LinearMap.det (B : E 2 →ₗ[ℝ] E 2) * LinearMap.det (A : E 2 →ₗ[ℝ] E 2) = 1 := by
    rw [← LinearMap.det_comp]
    have : (B : E 2 →ₗ[ℝ] E 2) ∘ₗ (A : E 2 →ₗ[ℝ] E 2) =
        ((B.comp A : E 2 →L[ℝ] E 2) : E 2 →ₗ[ℝ] E 2) := rfl
    rw [this, hBA]
    simp
  show LinearMap.det ((A : E 2 →ₗ[ℝ] E 2) ∘ₗ ((D : E 2 →ₗ[ℝ] E 2) ∘ₗ (B : E 2 →ₗ[ℝ] E 2))) = _
  rw [LinearMap.det_comp, LinearMap.det_comp]
  linear_combination (LinearMap.det (D : E 2 →ₗ[ℝ] E 2)) * h1

/-- R1 + Liouville: `retMap` fixes `p`, is `C³` there, with Jacobian `1`. -/
theorem retMap_facts {p : E 2} (hp : CertFacts p) :
    retMap p = p ∧ ContDiffAt ℝ 3 retMap p ∧ jdet retMap p = 1 := by
  obtain ⟨ρ, s, H₁, h₁, P₁, hρ, hs, hH, h0, hch, hP, hconj⟩ := R1_translate hp
  have hvf : ∀ t, hamVF (H₁ · t) 0 = 0 := fun t => by
    ext k; refine Fin.cases ?_ (fun l => ?_) k <;> simp [hamVF, (h0 t).2]
  obtain ⟨hsm, hdet⟩ := period_map_smooth hρ hs hH hvf hP hρ
  have hP0 : P₁ 0 = 0 := period_map_zero hρ hs hH (fun t => (h0 t).2) hP hρ
  obtain ⟨hh0, hball, hsrc, hcd, hcd'⟩ := hch
  have h0src : (0 : E 2) ∈ h₁.source := hball (mem_ball_self hρ)
  have hptgt : p ∈ h₁.target := hh0 ▸ h₁.map_source h0src
  have hsymm : h₁.symm p = 0 := hh0 ▸ h₁.left_inv h0src
  have hfix : retMap p = p := by
    have := hconj 0 (by simpa using hρ)
    rwa [hP0, hh0] at this
  have hev : retMap =ᶠ[𝓝 p] (h₁ ∘ P₁ ∘ h₁.symm) := by
    have hc : ContinuousAt h₁.symm p := h₁.continuousAt_symm hptgt
    have hb : ∀ᶠ y in 𝓝 p, h₁.symm y ∈ ball (0 : E 2) ρ :=
      hc.preimage_mem_nhds (by rw [hsymm]; exact ball_mem_nhds _ hρ)
    filter_upwards [hb, h₁.eventually_right_inverse hptgt] with y hy hy'
    have := hconj (h₁.symm y) (by simpa using hy)
    rw [hy'] at this
    exact this
  have hA : ContDiffAt ℝ ⊤ h₁ 0 := hcd.contDiffAt (hsrc.mem_nhds h0src)
  have hB : ContDiffAt ℝ ⊤ h₁.symm p := hcd'.contDiffAt (h₁.open_target.mem_nhds hptgt)
  have hA' : ContDiffAt ℝ ⊤ h₁ (P₁ (h₁.symm p)) := by rwa [hsymm, hP0]
  have hsm' : ContDiffAt ℝ ⊤ P₁ (h₁.symm p) := by rwa [hsymm]
  have hcomp : ContDiffAt ℝ ⊤ (h₁ ∘ P₁ ∘ h₁.symm) p := hA'.comp p (hsm'.comp p hB)
  refine ⟨hfix, (hcomp.congr_of_eventuallyEq hev).of_le le_top, ?_⟩
  have hne : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : fderiv ℝ retMap p =
      (fderiv ℝ h₁ 0).comp ((fderiv ℝ P₁ 0).comp (fderiv ℝ h₁.symm p)) := by
    rw [hev.fderiv_eq, fderiv_comp p (hA'.differentiableAt hne)
      ((hsm'.comp p hB).differentiableAt hne), fderiv_comp p (hsm'.differentiableAt hne)
      (hB.differentiableAt hne), Function.comp_apply, hsymm, hP0]
  have hBA : (fderiv ℝ h₁.symm p).comp (fderiv ℝ h₁ 0) = ContinuousLinearMap.id ℝ (E 2) := by
    have hid : (h₁.symm ∘ h₁) =ᶠ[𝓝 0] id := h₁.eventually_left_inverse h0src
    have := fderiv_comp (0 : E 2) (𝕜 := ℝ) (g := h₁.symm) (f := h₁)
      (by rw [hh0]; exact hB.differentiableAt hne) (hA.differentiableAt hne)
    rw [hid.fderiv_eq, fderiv_id, hh0] at this
    exact this.symm
  unfold jdet
  rw [hfd, det_sandwich _ _ _ hBA]
  exact hdet

theorem phi_contDiff : ContDiff ℝ ⊤ phi := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simp only [phi]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have h0 : ContDiff ℝ ⊤ (fun x : E 2 => x 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
    have h1 : ContDiff ℝ ⊤ (fun x : E 2 => x 1) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
    exact (h0.mul (Real.contDiff_sin.comp h1)).add (Real.contDiff_sin.comp h0)
  · simp only [phi]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff

/-- The derivative of `Φ` at `p` is injective when `sin p₁ + cos p₀ ≠ 0`. -/
theorem fderiv_phi_injective {p : E 2} (hp : Real.sin (p 1) + Real.cos (p 0) ≠ 0) :
    Function.Injective (fderiv ℝ phi p) := by
  have hd : HasFDerivAt phi (fderiv ℝ phi p) p :=
    (phi_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  set c0 : E 2 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  set c1 : E 2 →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  have e0 : ∀ u, c0 (fderiv ℝ phi p u) =
      p 0 * (Real.cos (p 1) * u 1) + Real.sin (p 1) * u 0 + Real.cos (p 0) * u 0 := by
    intro u
    have h1 := (c0.hasFDerivAt.comp p hd)
    have h2 : HasFDerivAt (fun x : E 2 => x 0 * Real.sin (x 1) + Real.sin (x 0)) _ p :=
      (c0.hasFDerivAt.mul (c1.hasFDerivAt.sin)).add c0.hasFDerivAt.sin
    have he : (c0 ∘ phi) = fun x : E 2 => x 0 * Real.sin (x 1) + Real.sin (x 0) := by
      funext x; simp [c0, phi]
    rw [he] at h1
    have := congrArg (fun L => L u) (h1.unique h2)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]
    simp [c0, c1]
  have e1 : ∀ u, c1 (fderiv ℝ phi p u) = u 1 := by
    intro u
    have h1 := (c1.hasFDerivAt.comp p hd)
    have he : (c1 ∘ phi) = fun x : E 2 => x 1 := by
      funext x; simp [c1, phi]
    rw [he] at h1
    have := congrArg (fun L => L u) (h1.unique c1.hasFDerivAt)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]
    simp [c1]
  refine (injective_iff_map_eq_zero (fderiv ℝ phi p)).2 fun u hu' => ?_
  have a1 := e1 u
  have a0 := e0 u
  rw [hu', map_zero] at a1 a0
  have hu1 : u 1 = 0 := a1.symm
  rw [hu1] at a0
  have hu0 : u 0 = 0 := by
    have : (Real.sin (p 1) + Real.cos (p 0)) * u 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp
    · exact h
  ext i
  fin_cases i
  · simpa using hu0
  · simpa using hu1

/-- `sin p₁ + cos p₀ ≥ 1.92` from the certified orbit at `t = 0`. -/
theorem phi_jac_pos {p : E 2} (hp : CertFacts p) : 192 / 100 ≤ Real.sin (p 1) + Real.cos (p 0) := by
  obtain ⟨γ, T, -, hγ0, hT, -, -, hz⟩ := hp.orbit
  have := hz 0 ⟨le_rfl, by linarith⟩
  rw [hγ0] at this
  simpa [abcField, lift] using this

end ABC.S4.TwistPhiAux
