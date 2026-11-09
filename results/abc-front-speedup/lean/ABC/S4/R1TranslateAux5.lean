import ABC.S4.R1Ham
import ABC.S4.R1TranslateAux3
import ABC.S4.R1TranslateAux4

/-! R1 helpers: the translated Hamiltonian
`H₁(w, t) = Hraw(Φ⁻¹(X*(t) + w), t) - Hraw(Q t, t) - symp(X*'(t), w)`, `X* = Φ ∘ Q`. -/

open Set Metric Filter Topology Real ComplexConjugate

noncomputable section

namespace ABC.S4.R1TranslateAux

/-- The derivative of `phiC`. -/
def phiCD (q : C2) : C2 →L[ℂ] C2 :=
  ContinuousLinearMap.pi ![(Complex.sin (q 1) + Complex.cos (q 0)) • ContinuousLinearMap.proj 0 +
    (q 0 * Complex.cos (q 1)) • ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 1]

lemma phiCD_apply (q v : C2) :
    phiCD q v = ![(Complex.sin (q 1) + Complex.cos (q 0)) * v 0 + q 0 * Complex.cos (q 1) * v 1,
      v 1] := by
  ext i; fin_cases i <;> simp [phiCD]

lemma hasFDerivAt_phiC (q : C2) : HasFDerivAt phiC (phiCD q) q := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · show HasFDerivAt (fun x => phiC x 0) ((ContinuousLinearMap.proj 0).comp (phiCD q)) q
    have h0 := hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) q
    have h1 := hasFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) q
    have := (h0.mul ((Complex.hasDerivAt_sin (q 1)).comp_hasFDerivAt q h1)).add
      ((Complex.hasDerivAt_sin (q 0)).comp_hasFDerivAt q h0)
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_fderiv ?_
    · simp [phiC]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [phiCD]; ring
  · simpa [phiC, phiCD] using hasFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) q

/-- `ξ ↦ symp v ξ` as a continuous linear map. -/
def sympL (v : C2) : C2 →L[ℂ] ℂ :=
  v 0 • ContinuousLinearMap.proj 1 - v 1 • ContinuousLinearMap.proj 0

lemma sympL_apply (v ξ : C2) : sympL v ξ = symp v ξ := by
  simp [sympL, symp]

lemma hamVF_eq {H : C2 → ℂ} {v w : C2} (h : HasFDerivAt H (sympL v) w) : hamVF H w = v := by
  rw [hamVF, h.fderiv]
  ext i; fin_cases i <;> simp [sympL]

lemma differentiable_Hraw : Differentiable ℂ (fun x : C2 × ℂ => Hraw x.1 x.2) := by
  unfold Hraw
  fun_prop

lemma differentiable_Hraw' (z : ℂ) : Differentiable ℂ (fun q : C2 => Hraw q z) := by
  unfold Hraw
  fun_prop

lemma Hraw_add_two_pi (q : C2) (z : ℂ) : Hraw q (z + 2 * π) = Hraw q z := by
  simp [Hraw, Complex.sin_add_two_pi, Complex.cos_add_two_pi]

lemma zField_add_two_pi (q : C2) (z : ℂ) : zField q (z + 2 * π) = zField q z := by
  simp [zField, Complex.sin_add_two_pi, Complex.cos_add_two_pi]

lemma Hraw_conj (q : C2) (z : ℂ) : conj (Hraw q z) = Hraw (cconj q) (conj z) := by
  simp [Hraw, cconj, Complex.sin_conj, Complex.cos_conj]

lemma zField_conj (q : C2) (z : ℂ) : cconj (zField q z) = zField (cconj q) (conj z) := by
  ext i; fin_cases i <;> simp [zField, cconj, Complex.sin_conj, Complex.cos_conj]

lemma phiCD_conj (q v : C2) : cconj (phiCD q v) = phiCD (cconj q) (cconj v) := by
  ext i; fin_cases i <;> simp [phiCD_apply, cconj, Complex.sin_conj, Complex.cos_conj]

lemma symp_conj (a b : C2) : conj (symp a b) = symp (cconj a) (cconj b) := by
  simp [symp, cconj]

lemma cconj_ofR (x : E 2) : cconj (ofR x) = ofR x := by
  ext i; simp [cconj, ofR]

/-- The output of `complex_orbit`. -/
structure OrbitData (p : E 2) (s M : ℝ) (Q : ℂ → C2) : Prop where
  pos : 0 < s
  per : ∀ t, Q (t + 2 * π) = Q t
  deriv : ∀ t ∈ strip s, HasDerivAt Q (zField (Q t) t) t
  bound : ∀ t ∈ strip s, ‖Q t‖ ≤ M ∧ 1 ≤ ‖Complex.sin (Q t 1) + Complex.cos (Q t 0)‖
  orbit : ∀ t : ℝ, t ∈ Icc 0 (2 * π) → Q t = ofR (crossP p t)
  real : ∀ t : ℝ, ∃ x : E 2, Q t = ofR x

/-- `X*'(t) = DΦ(Q t) zField(Q t, t)`. -/
def Vf (Q : ℂ → C2) (t : ℂ) : C2 := phiCD (Q t) (zField (Q t) t)

/-- The translated Hamiltonian (zero off the strip). -/
def H1 (M s : ℝ) (Q : ℂ → C2) (w : C2) (t : ℂ) : ℂ :=
  if |t.im| < s then Hraw (psi M w (Q t)) t - Hraw (Q t) t - symp (Vf Q t) w else 0

section H1

variable {p : E 2} {s M : ℝ} {Q : ℂ → C2} (hO : OrbitData p s M Q)
include hO

lemma OrbitData.M_nonneg : 0 ≤ M :=
  (norm_nonneg _).trans (hO.bound 0 (by simpa [strip] using hO.pos)).1

lemma OrbitData.mem_D {w : C2} (hw : ‖w‖ < r1 M) {t : ℂ} (ht : t ∈ strip s) :
    (w, Q t) ∈ Dset M := by
  obtain ⟨h1, h2⟩ := hO.bound t ht
  exact ⟨hw, by simp; linarith, by simp; linarith⟩

lemma OrbitData.rho_ne {t : ℂ} (ht : t ∈ strip s) :
    Complex.sin (Q t 1) + Complex.cos (Q t 0) ≠ 0 := by
  intro h; have := (hO.bound t ht).2; rw [h, norm_zero] at this; norm_num at this

lemma OrbitData.diffAt_Q {t : ℂ} (ht : t ∈ strip s) : DifferentiableAt ℂ Q t :=
  (hO.deriv t ht).differentiableAt

lemma OrbitData.diffAt_Vf {t : ℂ} (ht : t ∈ strip s) (i : Fin 2) :
    DifferentiableAt ℂ (fun t => Vf Q t i) t := by
  have hQ : ∀ j : Fin 2, DifferentiableAt ℂ (fun t => Q t j) t := fun j =>
    (differentiableAt_apply (𝕜 := ℂ) j (Q t)).comp t (hO.diffAt_Q ht)
  have hrho : DifferentiableAt ℂ (fun t => Complex.sin (Q t 1) + Complex.cos (Q t 0)) t :=
    ((Complex.differentiable_sin _).comp t (hQ 1)).add ((Complex.differentiable_cos _).comp t (hQ 0))
  have hz0 : DifferentiableAt ℂ (fun t => zField (Q t) t 0) t := by
    simp only [zField, Matrix.cons_val_zero]
    exact (((Complex.differentiable_sin _).comp t differentiableAt_id).add
      ((Complex.differentiable_cos _).comp t (hQ 1))).div hrho (hO.rho_ne ht)
  have hz1 : DifferentiableAt ℂ (fun t => zField (Q t) t 1) t := by
    simp only [zField, Matrix.cons_val_one]
    exact (((Complex.differentiable_sin _).comp t (hQ 0)).add
      ((Complex.differentiable_cos _).comp t differentiableAt_id)).div hrho (hO.rho_ne ht)
  fin_cases i
  · simp only [Vf, phiCD_apply, Matrix.cons_val_zero]
    exact (hrho.mul hz0).add (((hQ 0).mul ((Complex.differentiable_cos _).comp t (hQ 1))).mul hz1)
  · simpa [Vf, phiCD_apply] using hz1

lemma OrbitData.diffAt_formula {w₀ : C2} (hw : ‖w₀‖ < r1 M) {t₀ : ℂ} (ht : t₀ ∈ strip s) :
    DifferentiableAt ℂ (fun x : C2 × ℂ =>
      Hraw (psi M x.1 (Q x.2)) x.2 - Hraw (Q x.2) x.2 - symp (Vf Q x.2) x.1) (w₀, t₀) := by
  have hM := hO.M_nonneg
  have hQ : DifferentiableAt ℂ (fun x : C2 × ℂ => Q x.2) (w₀, t₀) :=
    (hO.diffAt_Q ht).comp _ differentiableAt_snd
  have hQi : ∀ j : Fin 2, DifferentiableAt ℂ (fun x : C2 × ℂ => Q x.2 j) (w₀, t₀) := fun j =>
    differentiableAt_pi.1 hQ j
  have hwi : ∀ j : Fin 2, DifferentiableAt ℂ (fun x : C2 × ℂ => x.1 j) (w₀, t₀) := fun j =>
    differentiableAt_pi.1 differentiableAt_fst j
  have hU : DifferentiableAt ℂ (fun x : C2 × ℂ => Ufn M x.1 (Q x.2)) (w₀, t₀) := by
    have h1 : DifferentiableAt ℂ (fun x : C2 × C2 => Ufn M x.1 x.2) (w₀, Q t₀) :=
      (Ufn_holo hM).differentiableAt ((isOpen_Dset M).mem_nhds (hO.mem_D hw ht))
    exact h1.comp (f := fun x : C2 × ℂ => (x.1, Q x.2)) _ (differentiableAt_fst.prodMk hQ)
  have hpsi : DifferentiableAt ℂ (fun x : C2 × ℂ => psi M x.1 (Q x.2)) (w₀, t₀) := by
    rw [differentiableAt_pi]
    intro i; fin_cases i
    · show DifferentiableAt ℂ (fun x : C2 × ℂ => Q x.2 0 + Ufn M x.1 (Q x.2)) (w₀, t₀)
      exact (hQi 0).add hU
    · show DifferentiableAt ℂ (fun x : C2 × ℂ => Q x.2 1 + x.1 1) (w₀, t₀)
      exact (hQi 1).add (hwi 1)
  have hH1 : DifferentiableAt ℂ (fun x : C2 × ℂ => Hraw (psi M x.1 (Q x.2)) x.2) (w₀, t₀) :=
    differentiable_Hraw.differentiableAt.comp (f := fun x : C2 × ℂ => (psi M x.1 (Q x.2), x.2))
      _ (hpsi.prodMk differentiableAt_snd)
  have hH2 : DifferentiableAt ℂ (fun x : C2 × ℂ => Hraw (Q x.2) x.2) (w₀, t₀) :=
    differentiable_Hraw.differentiableAt.comp (f := fun x : C2 × ℂ => (Q x.2, x.2))
      _ (hQ.prodMk differentiableAt_snd)
  have hV : ∀ j : Fin 2, DifferentiableAt ℂ (fun x : C2 × ℂ => Vf Q x.2 j) (w₀, t₀) := fun j =>
    DifferentiableAt.comp (g := fun t => Vf Q t j) (f := fun x : C2 × ℂ => x.2) (w₀, t₀)
      (hO.diffAt_Vf ht j) differentiableAt_snd
  have hS : DifferentiableAt ℂ (fun x : C2 × ℂ => symp (Vf Q x.2) x.1) (w₀, t₀) := by
    simp only [symp]
    exact ((hV 0).mul (hwi 1)).sub ((hV 1).mul (hwi 0))
  exact (hH1.sub hH2).sub hS

/-- The key identity: `Hraw ∘ Φ⁻¹` has gradient `symp(DΦ zField, ·)` (via `R1_hamiltonian`). -/
lemma hasFDerivAt_G {w₀ b : C2} (hx : (w₀, b) ∈ Dset M) (t : ℂ) :
    HasFDerivAt (fun w => Hraw (psi M w b) t)
      (sympL (phiCD (psi M w₀ b) (zField (psi M w₀ b) t))) w₀ := by
  have hM := hO.M_nonneg
  set ψ := fun w => psi M w b with hψ
  have hopen : {w : C2 | (w, b) ∈ Dset M} ∈ 𝓝 w₀ :=
    ((isOpen_Dset M).preimage (continuous_id.prodMk continuous_const)).mem_nhds hx
  have hdψ : DifferentiableAt ℂ ψ w₀ := by
    have hU : DifferentiableAt ℂ (fun w => Ufn M w b) w₀ := by
      have h1 : DifferentiableAt ℂ (fun x : C2 × C2 => Ufn M x.1 x.2) (w₀, b) :=
        (Ufn_holo hM).differentiableAt ((isOpen_Dset M).mem_nhds hx)
      exact h1.comp (f := fun w : C2 => (w, b)) _
        (differentiableAt_id.prodMk (differentiableAt_const _))
    rw [differentiableAt_pi]
    intro i; fin_cases i
    · simpa [ψ, psi] using hU.const_add (b 0)
    · simpa [ψ, psi] using ((differentiableAt_apply (𝕜 := ℂ) 1 w₀).const_add (b 1))
  set Dψ := fderiv ℂ ψ w₀
  have hψd : HasFDerivAt ψ Dψ w₀ := hdψ.hasFDerivAt
  -- `Φ ∘ ψ = Φ b + id` near `w₀`
  have hid : (phiCD (ψ w₀)).comp Dψ = ContinuousLinearMap.id ℂ C2 := by
    have h1 : HasFDerivAt (fun w => phiC (ψ w)) ((phiCD (ψ w₀)).comp Dψ) w₀ :=
      (hasFDerivAt_phiC _).comp w₀ hψd
    have h2 : HasFDerivAt (fun w => phiC (ψ w)) (ContinuousLinearMap.id ℂ C2) w₀ := by
      have := (hasFDerivAt_id (𝕜 := ℂ) w₀).const_add (phiC b)
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [hopen] with w hw
      exact phiC_psi hM hw
    exact h1.unique h2
  have hH : HasFDerivAt (fun w => Hraw (ψ w) t)
      ((fderiv ℂ (fun q => Hraw q t) (ψ w₀)).comp Dψ) w₀ :=
    ((differentiable_Hraw' t) _).hasFDerivAt.comp w₀ hψd
  convert hH using 1
  ext ξ
  have hq : Complex.sin (ψ w₀ 1) + Complex.cos (ψ w₀ 0) ≠ 0 := by
    intro h; have := psi_rho hM hx; simp only [ψ] at h; rw [h, norm_zero] at this
    norm_num at this
  have hR := R1_hamiltonian (ψ w₀) t hq (Dψ ξ)
  have hD : fderiv ℂ phiC (ψ w₀) = phiCD (ψ w₀) := (hasFDerivAt_phiC _).fderiv
  have hξ : phiCD (ψ w₀) (Dψ ξ) = ξ := by
    have := congrArg (fun L : C2 →L[ℂ] C2 => L ξ) hid
    simpa using this
  rw [hD, hξ] at hR
  rw [ContinuousLinearMap.comp_apply, ← hR, sympL_apply]

lemma OrbitData.H1_eq {t : ℂ} (ht : t ∈ strip s) :
    (fun w => H1 M s Q w t) =
      fun w => Hraw (psi M w (Q t)) t - Hraw (Q t) t - symp (Vf Q t) w := by
  funext w; simp only [H1, if_pos (show |t.im| < s from ht)]

/-- The derivative of `H₁(·, t)` at a point of the polydisc. -/
lemma OrbitData.hasFDerivAt_H1 {w₀ : C2} (hw : ‖w₀‖ < r1 M) {t : ℂ} (ht : t ∈ strip s) :
    HasFDerivAt (fun w => H1 M s Q w t)
      (sympL (phiCD (psi M w₀ (Q t)) (zField (psi M w₀ (Q t)) t)) - sympL (Vf Q t)) w₀ := by
  rw [hO.H1_eq ht]
  have h := (hasFDerivAt_G hO (hO.mem_D hw ht) t).sub_const (Hraw (Q t) t)
  have hs : HasFDerivAt (fun w => symp (Vf Q t) w) (sympL (Vf Q t)) w₀ := by
    exact (sympL (Vf Q t)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w => (sympL_apply _ _).symm)
  exact h.sub hs

lemma OrbitData.isTPHam {ρ : ℝ} (hρ : ρ ≤ r1 M) : IsTPHam (H1 M s Q) ρ s where
  holo := by
    intro x hx
    obtain ⟨hw, ht⟩ := hx
    have hw' : ‖x.1‖ < r1 M := lt_of_lt_of_le hw hρ
    refine (hO.diffAt_formula hw' ht).differentiableWithinAt.congr (fun y hy => ?_) ?_
    · simp only [H1, if_pos (show |y.2.im| < s from hy.2)]
    · simp only [H1, if_pos (show |x.2.im| < s from ht)]
  real := by
    intro x t hx
    have hM := hO.M_nonneg
    have hts : (t : ℂ) ∈ strip s := by simpa [strip] using hO.pos
    obtain ⟨y, hy⟩ := hO.real t
    have hxD : (ofR x, Q t) ∈ Dset M := hO.mem_D (lt_of_lt_of_le hx hρ) hts
    rw [← Complex.conj_eq_iff_im]
    simp only [H1, if_pos (show |(t : ℂ).im| < s from hts), map_sub, Hraw_conj, symp_conj,
      Complex.conj_ofReal]
    have h1 : cconj (psi M (ofR x) (Q t)) = psi M (ofR x) (Q t) := by
      rw [← psi_cconj hM hxD, cconj_ofR, hy, cconj_ofR]
    have h2 : cconj (Q t) = Q t := by rw [hy, cconj_ofR]
    have h3 : cconj (Vf Q t) = Vf Q t := by
      simp only [Vf]; rw [phiCD_conj, zField_conj, h2, Complex.conj_ofReal]
    rw [h1, h2, h3, cconj_ofR]
  per := by
    intro w t
    have him : (t + 2 * π).im = t.im := by simp
    simp only [H1, him, hO.per, Vf, Hraw_add_two_pi, zField_add_two_pi]

lemma OrbitData.H1_zero (t : ℂ) : H1 M s Q 0 t = 0 ∧ fderiv ℂ (fun w => H1 M s Q w t) 0 = 0 := by
  have hM := hO.M_nonneg
  by_cases ht : t ∈ strip s
  · have h0 : ‖(0 : C2)‖ < r1 M := by simpa using r1_pos hM
    have hp0 := psi_zero hM (hO.mem_D h0 ht)
    refine ⟨?_, ?_⟩
    · simp only [H1, if_pos (show |t.im| < s from ht), hp0]; simp [symp]
    · rw [(hO.hasFDerivAt_H1 h0 ht).fderiv, hp0]
      simp [Vf]
  · have hf : (fun w => H1 M s Q w t) = fun _ => 0 := by
      funext w; simp only [H1, if_neg (show ¬ |t.im| < s from ht)]
    refine ⟨by simpa using congrFun hf 0, ?_⟩
    rw [hf]; simp

end H1

end ABC.S4.R1TranslateAux
