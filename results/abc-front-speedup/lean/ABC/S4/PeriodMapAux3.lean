import ABC.S4.PeriodMapAux1
import ABC.Twist

/-! Liouville: a trace-free holomorphic flow on `ℂ³` has Jacobian determinant `1`. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.PeriodMapAux

open ABC

def e3 (j : Fin 3) : Cn 3 := Pi.single j 1

-- the Jacobian matrix of `L`
def jmat (L : Cn 3 →L[ℂ] Cn 3) : Matrix (Fin 3) (Fin 3) ℂ := fun i j => L (e3 j) i

lemma vec3_eq (v : Cn 3) : v = v 0 • e3 0 + v 1 • e3 1 + v 2 • e3 2 := by
  funext i; fin_cases i <;> simp [e3]

lemma clm3_apply (L : Cn 3 →L[ℂ] Cn 3) (v : Cn 3) (i : Fin 3) :
    L v i = v 0 * L (e3 0) i + v 1 * L (e3 1) i + v 2 * L (e3 2) i := by
  conv_lhs => rw [vec3_eq v]
  simp

lemma liouville {F : Cn 3 → Cn 3} {U : Set (Cn 3)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U)
    (htr : ∀ q ∈ U, fderiv ℂ F q (e3 0) 0 + fderiv ℂ F q (e3 1) 1 + fderiv ℂ F q (e3 2) 2 = 0)
    {W : Set ℂ} (hW : IsOpen W) (hWc : IsPreconnected W) (hW0 : (0 : ℂ) ∈ W)
    {r : ℝ} (hr : 0 < r) {φ : ℂ → Cn 3 → Cn 3}
    (hφ : DifferentiableOn ℂ (fun p : ℂ × Cn 3 => φ p.1 p.2) (W ×ˢ ball 0 r))
    (hφ0 : ∀ x ∈ ball (0 : Cn 3) r, φ 0 x = x)
    (hφd : ∀ x ∈ ball (0 : Cn 3) r, ∀ t ∈ W, HasDerivAt (φ · x) (F (φ t x)) t ∧ φ t x ∈ U)
    {t : ℂ} (ht : t ∈ W) : (jmat (fderiv ℂ (φ t) 0)).det = 1 := by
  set Ψ : ℂ × Cn 3 → Cn 3 := fun p => φ p.1 p.2
  set V := W ×ˢ ball (0 : Cn 3) r
  have hV : IsOpen V := hW.prod isOpen_ball
  have h0r : (0 : Cn 3) ∈ ball (0 : Cn 3) r := mem_ball_self hr
  have hmem : ∀ t ∈ W, ((t, 0) : ℂ × Cn 3) ∈ V := fun t ht => ⟨ht, h0r⟩
  have hΨd : ∀ p ∈ V, DifferentiableAt ℂ Ψ p := fun p hp => (hφ p hp).differentiableAt
    (hV.mem_nhds hp)
  have hDΨ : DifferentiableOn ℂ (fderiv ℂ Ψ) V := differentiableOn_fderiv hV hφ
  -- the partial derivative in `x`
  have hx : ∀ t ∈ W, ∀ v, fderiv ℂ (φ t) 0 v = fderiv ℂ Ψ (t, 0) (0, v) := by
    intro t ht v
    have h1 : HasFDerivAt (fun y : Cn 3 => ((t, y) : ℂ × Cn 3)) (ContinuousLinearMap.inr ℂ ℂ (Cn 3)) 0 :=
      (hasFDerivAt_const t 0).prodMk (hasFDerivAt_id 0)
    have h2 := (hΨd _ (hmem t ht)).hasFDerivAt.comp (0 : Cn 3) h1
    rw [show φ t = Ψ ∘ fun y : Cn 3 => ((t, y) : ℂ × Cn 3) from rfl, h2.fderiv]
    rfl
  -- the partial derivative in `t` is the field
  have htime : ∀ p ∈ V, fderiv ℂ Ψ p (1, 0) = F (Ψ p) := by
    intro p hp
    have h1 : HasDerivAt (fun s : ℂ => ((s, p.2) : ℂ × Cn 3)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have h2 := (hΨd p hp).hasFDerivAt.comp_hasDerivAt p.1 h1
    exact h2.unique (hφd p.2 hp.2 p.1 hp.1).1
  -- variational equation
  have hvar : ∀ t ∈ W, ∀ v, HasDerivAt (fun s => fderiv ℂ Ψ (s, 0) (0, v))
      (fderiv ℂ F (Ψ (t, 0)) (fderiv ℂ Ψ (t, 0) (0, v))) t := by
    intro t ht v
    have hpn := hV.mem_nhds (hmem t ht)
    have hD2 : DifferentiableAt ℂ (fderiv ℂ Ψ) (t, 0) := (hDΨ _ (hmem t ht)).differentiableAt hpn
    have h1 : HasDerivAt (fun s : ℂ => ((s, 0) : ℂ × Cn 3)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t 0)
    have h2 : HasDerivAt (fun s => fderiv ℂ Ψ (s, 0) (0, v))
        (fderiv ℂ (fderiv ℂ Ψ) (t, 0) (1, 0) (0, v)) t :=
      (ContinuousLinearMap.apply ℂ (Cn 3) ((0 : ℂ), v)).hasFDerivAt.comp_hasDerivAt t
        (hD2.hasFDerivAt.comp_hasDerivAt t h1)
    convert h2 using 1
    have hsymm := ((analyticAt_of_differentiableOn hV hφ (hmem t ht)).contDiffAt
      (n := ⊤)).isSymmSndFDerivAt_of_omega
    rw [hsymm]
    -- `p ↦ DΨ p (1,0)` agrees with `F ∘ Ψ` near `(t, 0)`
    have hev : (fun p => fderiv ℂ Ψ p (1, 0)) =ᶠ[𝓝 (t, 0)] fun p => F (Ψ p) := by
      filter_upwards [hpn] with p hp
      exact htime p hp
    have hFd : DifferentiableAt ℂ F (Ψ (t, 0)) :=
      (hF _ (hφd 0 h0r t ht).2).differentiableAt (hU.mem_nhds (hφd 0 h0r t ht).2)
    have h3 := hev.fderiv_eq (𝕜 := ℂ)
    have h5 : HasFDerivAt (fun p => F (Ψ p))
        ((fderiv ℂ F (Ψ (t, 0))).comp (fderiv ℂ Ψ (t, 0))) (t, 0) :=
      hFd.hasFDerivAt.comp (t, (0 : Cn 3)) (hΨd _ (hmem t ht)).hasFDerivAt
    rw [fderiv_clm_apply hD2 (differentiableAt_const _), h5.fderiv] at h3
    have h4 := congrArg (fun L => L ((0 : ℂ), v)) h3
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp, Function.comp_apply] at h4
    exact h4.symm
  -- entries of the Jacobian matrix along `t`
  set m : ℂ → Fin 3 → Fin 3 → ℂ := fun s i j => fderiv ℂ Ψ (s, 0) (0, e3 j) i
  have hm : ∀ s ∈ W, jmat (fderiv ℂ (φ s) 0) = m s := by
    intro s hs; funext i j; simp only [jmat, m, hx s hs]
  set a : ℂ → Fin 3 → Fin 3 → ℂ := fun s i k => fderiv ℂ F (Ψ (s, 0)) (e3 k) i
  have hme : ∀ s ∈ W, ∀ i j, HasDerivAt (fun s => m s i j)
      (a s i 0 * m s 0 j + a s i 1 * m s 1 j + a s i 2 * m s 2 j) s := by
    intro s hs i j
    have h := hasDerivAt_pi.1 (hvar s hs (e3 j)) i
    convert h using 1
    rw [clm3_apply _ _ i]
    simp only [a, m]
    ring
  have htr' : ∀ s ∈ W, a s 0 0 + a s 1 1 + a s 2 2 = 0 := fun s hs =>
    htr _ (hφd 0 h0r s hs).2
  -- the determinant is constant
  set D : ℂ → ℂ := fun s => Matrix.det (m s)
  have hDd : ∀ s ∈ W, HasDerivAt D 0 s := by
    intro s hs
    have h00 := hme s hs 0 0; have h01 := hme s hs 0 1; have h02 := hme s hs 0 2
    have h10 := hme s hs 1 0; have h11 := hme s hs 1 1; have h12 := hme s hs 1 2
    have h20 := hme s hs 2 0; have h21 := hme s hs 2 1; have h22 := hme s hs 2 2
    have h := ((((((h00.mul h11).mul h22).sub ((h00.mul h12).mul h21)).sub
      ((h01.mul h10).mul h22)).add ((h01.mul h12).mul h20)).add ((h02.mul h10).mul h21)).sub
      ((h02.mul h11).mul h20)
    have hD : D = fun s => m s 0 0 * m s 1 1 * m s 2 2 - m s 0 0 * m s 1 2 * m s 2 1
        - m s 0 1 * m s 1 0 * m s 2 2 + m s 0 1 * m s 1 2 * m s 2 0
        + m s 0 2 * m s 1 0 * m s 2 1 - m s 0 2 * m s 1 1 * m s 2 0 := by
      funext s; exact Matrix.det_fin_three (m s)
    rw [hD]
    convert h using 1
    simp only [Pi.mul_apply]
    linear_combination (-(m s 0 0 * m s 1 1 * m s 2 2 - m s 0 0 * m s 1 2 * m s 2 1
        - m s 0 1 * m s 1 0 * m s 2 2 + m s 0 1 * m s 1 2 * m s 2 0
        + m s 0 2 * m s 1 0 * m s 2 1 - m s 0 2 * m s 1 1 * m s 2 0)) * htr' s hs
  have hconst : D t = D 0 := hW.is_const_of_deriv_eq_zero hWc
    (fun s hs => (hDd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hDd s hs).deriv) ht hW0
  -- at time `0` the flow is the identity
  have hid : fderiv ℂ (φ 0) 0 = ContinuousLinearMap.id ℂ (Cn 3) := by
    have hev : φ 0 =ᶠ[𝓝 0] id := by
      filter_upwards [isOpen_ball.mem_nhds h0r] with x hx
      exact hφ0 x hx
    rw [hev.fderiv_eq, fderiv_id]
  have hD0 : D 0 = 1 := by
    simp only [D, ← hm 0 hW0, hid, jmat, ContinuousLinearMap.id_apply, e3,
      Matrix.det_fin_three]
    simp
  rw [hm t ht]
  exact hconst.trans hD0

end ABC.S4.PeriodMapAux
