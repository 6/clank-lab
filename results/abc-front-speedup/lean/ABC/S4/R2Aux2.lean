import ABC.S4.PeriodMap
import ABC.S4.HoloDeriv
import ABC.S4.R2Aux1

/-! R2 helpers: partial derivatives of `H₁`, the Hessian `Amat` at `w = 0`, and the extended
autonomous field `Fvf` on `ℂ³` (state `(w, τ)`, `τ' = 1`). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

theorem hasDerivAt_ofReal_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {e : ℂ → E} {e' : E} {z : ℝ} (hf : HasDerivAt e e' (z : ℂ)) :
    HasDerivAt (fun y : ℝ => e y) e' z := by
  have := hf.scomp z (Complex.ofRealCLM.hasDerivAt (x := (z : ℝ)))
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at this
  exact this

theorem isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem isOpen_polydisc (ρ : ℝ) : IsOpen (polydisc ρ) :=
  isOpen_lt continuous_norm continuous_const

theorem isOpen_Ω (ρ s : ℝ) : IsOpen (polydisc ρ ×ˢ strip s) :=
  (isOpen_polydisc ρ).prod (isOpen_strip s)

def Hh (H₁ : C2 → ℂ → ℂ) : C2 × ℂ → ℂ := fun q => H₁ q.1 q.2

def eC (j : Fin 2) : C2 := Pi.single j 1

def P1 (H₁ : C2 → ℂ → ℂ) (j : Fin 2) (q : C2 × ℂ) : ℂ := fderiv ℂ (Hh H₁) q (eC j, 0)

def P2 (H₁ : C2 → ℂ → ℂ) (i j : Fin 2) (q : C2 × ℂ) : ℂ := fderiv ℂ (P1 H₁ j) q (eC i, 0)

/-- `∂ᵢ∂ⱼ H₁(0, t)`. -/
def Amat (H₁ : C2 → ℂ → ℂ) (t : ℂ) (i j : Fin 2) : ℂ :=
  fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC j)) 0 (eC i)

theorem eC_sum (u : C2) : u = u 0 • eC 0 + u 1 • eC 1 := by
  funext i; fin_cases i <;> simp [eC]

theorem hasFDerivAt_slice {K : C2 × ℂ → ℂ} {Ω : Set (C2 × ℂ)} (hΩ : IsOpen Ω)
    (hK : DifferentiableOn ℂ K Ω) {w : C2} {t : ℂ} (h : (w, t) ∈ Ω) :
    HasFDerivAt (fun w => K (w, t)) ((fderiv ℂ K (w, t)).comp (ContinuousLinearMap.inl ℂ C2 ℂ)) w :=
  (hK.differentiableAt (hΩ.mem_nhds h)).hasFDerivAt.comp w (hasFDerivAt_prodMk_left w t)

theorem fderiv_slice_apply {K : C2 × ℂ → ℂ} {Ω : Set (C2 × ℂ)} (hΩ : IsOpen Ω)
    (hK : DifferentiableOn ℂ K Ω) {w : C2} {t : ℂ} (h : (w, t) ∈ Ω) (v : C2) :
    fderiv ℂ (fun w => K (w, t)) w v = fderiv ℂ K (w, t) (v, 0) := by
  rw [(hasFDerivAt_slice hΩ hK h).fderiv]; rfl

theorem partial_holo {K : C2 × ℂ → ℂ} {Ω : Set (C2 × ℂ)} (hΩ : IsOpen Ω)
    (hK : DifferentiableOn ℂ K Ω) (v : C2 × ℂ) :
    DifferentiableOn ℂ (fun q => fderiv ℂ K q v) Ω := fun _ hq =>
  ((HoloDeriv.differentiableAt_fderiv hΩ hK hq).clm_apply
    (differentiableAt_const _)).differentiableWithinAt

section H

variable {H₁ : C2 → ℂ → ℂ} {ρ s : ℝ}

theorem Hh_holo (hH : IsTPHam H₁ ρ s) : DifferentiableOn ℂ (Hh H₁) (polydisc ρ ×ˢ strip s) :=
  hH.holo

theorem P1_holo (hH : IsTPHam H₁ ρ s) (j : Fin 2) :
    DifferentiableOn ℂ (P1 H₁ j) (polydisc ρ ×ˢ strip s) :=
  partial_holo (isOpen_Ω ρ s) (Hh_holo hH) _

theorem P2_holo (hH : IsTPHam H₁ ρ s) (i j : Fin 2) :
    DifferentiableOn ℂ (P2 H₁ i j) (polydisc ρ ×ˢ strip s) :=
  partial_holo (isOpen_Ω ρ s) (P1_holo hH j) _

theorem diffAt_slice (hH : IsTPHam H₁ ρ s) {w : C2} {t : ℂ} (h : (w, t) ∈ polydisc ρ ×ˢ strip s) :
    DifferentiableAt ℂ (H₁ · t) w :=
  (hasFDerivAt_slice (isOpen_Ω ρ s) (Hh_holo hH) h).differentiableAt

theorem diffOn_slice (hH : IsTPHam H₁ ρ s) {t : ℂ} (ht : t ∈ strip s) :
    DifferentiableOn ℂ (H₁ · t) (polydisc ρ) := fun _ hw =>
  (diffAt_slice hH (mk_mem_prod hw ht)).differentiableWithinAt

theorem d1_eq (hH : IsTPHam H₁ ρ s) {w : C2} {t : ℂ} (h : (w, t) ∈ polydisc ρ ×ˢ strip s)
    (j : Fin 2) : fderiv ℂ (H₁ · t) w (eC j) = P1 H₁ j (w, t) :=
  fderiv_slice_apply (K := Hh H₁) (isOpen_Ω ρ s) (Hh_holo hH) h (eC j)

theorem d1_eventuallyEq (hH : IsTPHam H₁ ρ s) {w : C2} {t : ℂ}
    (h : (w, t) ∈ polydisc ρ ×ˢ strip s) (j : Fin 2) :
    (fun w => fderiv ℂ (H₁ · t) w (eC j)) =ᶠ[𝓝 w] fun w => P1 H₁ j (w, t) := by
  filter_upwards [(isOpen_polydisc ρ).mem_nhds h.1] with w' hw'
  exact d1_eq hH (mk_mem_prod hw' h.2) j

theorem d1_diffAt (hH : IsTPHam H₁ ρ s) {w : C2} {t : ℂ}
    (h : (w, t) ∈ polydisc ρ ×ˢ strip s) (j : Fin 2) :
    DifferentiableAt ℂ (fun w => fderiv ℂ (H₁ · t) w (eC j)) w :=
  ((hasFDerivAt_slice (isOpen_Ω ρ s) (P1_holo hH j) h).differentiableAt).congr_of_eventuallyEq
    (d1_eventuallyEq hH h j)

theorem Amat_eq (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ strip s) (i j : Fin 2) :
    Amat H₁ t i j = P2 H₁ i j (0, t) := by
  have h : ((0 : C2), t) ∈ polydisc ρ ×ˢ strip s := mk_mem_prod (by simp [polydisc, hρ]) ht
  unfold Amat
  rw [(d1_eventuallyEq hH h j).fderiv_eq]
  exact fderiv_slice_apply (K := P1 H₁ j) (isOpen_Ω ρ s) (P1_holo hH j) h (eC i)

theorem Amat_holo (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (i j : Fin 2) :
    DifferentiableOn ℂ (fun t => Amat H₁ t i j) (strip s) := by
  have : DifferentiableOn ℂ (fun t => P2 H₁ i j (0, t)) (strip s) :=
    (P2_holo hH i j).comp (differentiableOn_const _ |>.prodMk differentiableOn_id)
      fun t ht => mk_mem_prod (by simp [polydisc, hρ]) ht
  exact this.congr fun t ht => Amat_eq hH hρ ht i j

theorem Amat_per (hH : IsTPHam H₁ ρ s) (t : ℂ) : Amat H₁ (t + 2 * π) = Amat H₁ t := by
  unfold Amat
  rw [show (H₁ · (t + 2 * π)) = (H₁ · t) from funext fun w => hH.per w t]

theorem Amat_symm (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ strip s) (i j : Fin 2) :
    Amat H₁ t i j = Amat H₁ t j i := by
  have h0 : (0 : C2) ∈ polydisc ρ := by simp [polydisc, hρ]
  have hc : ContDiffAt ℂ ∞ (H₁ · t) 0 :=
    HoloDeriv.contDiffAt (isOpen_polydisc ρ) (diffOn_slice hH ht) h0
  have hsymm : IsSymmSndFDerivAt ℂ (H₁ · t) 0 :=
    hc.isSymmSndFDerivAt (by simp)
  have hdf : DifferentiableAt ℂ (fderiv ℂ (H₁ · t)) 0 :=
    HoloDeriv.differentiableAt_fderiv (isOpen_polydisc ρ) (diffOn_slice hH ht) h0
  have key : ∀ i j, Amat H₁ t i j = fderiv ℂ (fderiv ℂ (H₁ · t)) 0 (eC i) (eC j) := by
    intro i j
    unfold Amat
    rw [fderiv_clm_apply hdf (differentiableAt_const _)]
    simp
  rw [key, key, hsymm]

/-- Points with real coordinates in the polydisc are `ofR` points. -/
theorem real_pt (hH : IsTPHam H₁ ρ s) {y : C2} (hy : ∀ i, (y i).im = 0) (hyρ : ‖y‖ < ρ)
    (t : ℝ) : (H₁ y t).im = 0 := by
  have hy' : y = ofR !₂[(y 0).re, (y 1).re] := by
    funext i; fin_cases i <;> simp [ofR, Complex.ext_iff, hy]
  rw [hy'] at hyρ ⊢
  exact hH.real _ t hyρ

theorem d1_real (hH : IsTPHam H₁ ρ s) (hs : 0 < s) {y : C2} (hy : ∀ i, (y i).im = 0)
    (hyρ : ‖y‖ < ρ) (t : ℝ) (j : Fin 2) : (fderiv ℂ (H₁ · (t : ℂ)) y (eC j)).im = 0 := by
  have hts : (t : ℂ) ∈ strip s := by simp [strip, hs]
  refine R2Aux.im_fderiv_eq_zero hy (diffAt_slice hH (mk_mem_prod hyρ hts)) ?_ j
  filter_upwards [(isOpen_polydisc ρ).mem_nhds (show y ∈ polydisc ρ from hyρ)] with z hz hzr
  exact real_pt hH hzr hz t

theorem Amat_real (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hs : 0 < s) (t : ℝ) (i j : Fin 2) :
    (Amat H₁ t i j).im = 0 := by
  have hts : (t : ℂ) ∈ strip s := by simp [strip, hs]
  have h0 : ((0 : C2), (t : ℂ)) ∈ polydisc ρ ×ˢ strip s :=
    mk_mem_prod (by simp [polydisc, hρ]) hts
  refine R2Aux.im_fderiv_eq_zero (fun i => by simp) (d1_diffAt hH h0 j) ?_ i
  filter_upwards [(isOpen_polydisc ρ).mem_nhds h0.1] with z hz hzr
  exact d1_real hH hs hzr hz t j

/-- `∂_u ∂ⱼ H₁(0,t) = Σₖ uₖ Aₖⱼ`. -/
theorem hasFDerivAt_d1 (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ strip s)
    (j : Fin 2) :
    HasFDerivAt (fun w => fderiv ℂ (H₁ · t) w (eC j))
      (fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC j)) 0) 0 ∧
    ∀ u : C2, fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC j)) 0 u =
      u 0 * Amat H₁ t 0 j + u 1 * Amat H₁ t 1 j := by
  have h0 : ((0 : C2), t) ∈ polydisc ρ ×ˢ strip s := mk_mem_prod (by simp [polydisc, hρ]) ht
  refine ⟨(d1_diffAt hH h0 j).hasFDerivAt, fun u => ?_⟩
  conv_lhs => rw [eC_sum u]
  simp [Amat]

end H

/-! The extended field on `ℂ³`. -/

def wPart (y : Cn 3) : C2 := fun i => y (Fin.castSucc i)

def Fvf (H₁ : C2 → ℂ → ℂ) (y : Cn 3) : Cn 3 :=
  ![hamVF (H₁ · (y 2)) (wPart y) 0, hamVF (H₁ · (y 2)) (wPart y) 1, 1]

def Uset (ρ s : ℝ) : Set (Cn 3) := {y | wPart y ∈ polydisc ρ ∧ y 2 ∈ strip s}

def proj3 (y : Cn 3) : C2 × ℂ := (wPart y, y 2)

theorem wPart_diff : Differentiable ℂ wPart :=
  differentiable_pi.2 fun _ => differentiable_apply _

theorem proj3_diff : Differentiable ℂ proj3 :=
  wPart_diff.prodMk (differentiable_apply _)

theorem isOpen_Uset (ρ s : ℝ) : IsOpen (Uset ρ s) :=
  (isOpen_Ω ρ s).preimage proj3_diff.continuous

theorem proj3_mem {ρ s : ℝ} {y : Cn 3} (hy : y ∈ Uset ρ s) : proj3 y ∈ polydisc ρ ×ˢ strip s :=
  hy

section F

variable {H₁ : C2 → ℂ → ℂ} {ρ s : ℝ}

theorem Fvf_eq (hH : IsTPHam H₁ ρ s) {y : Cn 3} (hy : y ∈ Uset ρ s) :
    Fvf H₁ y = ![P1 H₁ 1 (proj3 y), -P1 H₁ 0 (proj3 y), 1] := by
  have h := proj3_mem hy
  simp only [Fvf, hamVF]
  rw [show (Pi.single 1 1 : C2) = eC 1 from rfl, show (Pi.single 0 1 : C2) = eC 0 from rfl,
    d1_eq hH h, d1_eq hH h]
  rfl

theorem Fvf_holo (hH : IsTPHam H₁ ρ s) : DifferentiableOn ℂ (Fvf H₁) (Uset ρ s) := by
  have hR : DifferentiableOn ℂ (fun y => ![P1 H₁ 1 (proj3 y), -P1 H₁ 0 (proj3 y), 1]) (Uset ρ s) := by
    refine differentiableOn_pi.2 fun i => ?_
    have h1 := (P1_holo hH 1).comp proj3_diff.differentiableOn fun y hy => proj3_mem hy
    have h0 := (P1_holo hH 0).comp proj3_diff.differentiableOn fun y hy => proj3_mem hy
    fin_cases i
    · exact h1
    · exact h0.neg
    · exact differentiableOn_const _
  exact hR.congr fun y hy => Fvf_eq hH hy

def axisPt (t : ℂ) : Cn 3 := ![0, 0, t]

theorem wPart_axis (t : ℂ) : wPart (axisPt t) = 0 := by
  funext i; fin_cases i <;> rfl

theorem axis_mem (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ strip s) : axisPt t ∈ Uset ρ s :=
  ⟨by rw [wPart_axis]; simp [polydisc, hρ], ht⟩

theorem Fvf_axis (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (t : ℂ) :
    Fvf H₁ (axisPt t) = ![0, 0, 1] := by
  have h2 : axisPt t 2 = t := rfl
  simp only [Fvf, hamVF, h2, wPart_axis, (h0 t).2]
  simp

/-- The linearisation of `Fvf` along the axis, on vectors with zero `τ`-component. -/
theorem fderiv_Fvf_axis (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ strip s)
    {y : Cn 3} (hy : y 2 = 0) :
    fderiv ℂ (Fvf H₁) (axisPt t) y =
      ![y 0 * Amat H₁ t 0 1 + y 1 * Amat H₁ t 1 1,
        -(y 0 * Amat H₁ t 0 0 + y 1 * Amat H₁ t 1 0), 0] := by
  set ι : C2 → Cn 3 := fun w => ![w 0, w 1, t]
  set ιL : C2 →L[ℂ] Cn 3 := ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]
  have hι : HasFDerivAt ι ιL 0 := by
    refine hasFDerivAt_pi.2 fun i => ?_
    fin_cases i
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).hasFDerivAt
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).hasFDerivAt
    · simpa using hasFDerivAt_const t (0 : C2)
  have hι0 : ι 0 = axisPt t := by funext i; fin_cases i <;> rfl
  have hcomp : Fvf H₁ ∘ ι = fun w =>
      ![fderiv ℂ (H₁ · t) w (eC 1), -fderiv ℂ (H₁ · t) w (eC 0), 1] := by
    funext w
    have hw : wPart (ι w) = w := by funext i; fin_cases i <;> rfl
    have h2 : ι w 2 = t := rfl
    simp only [Function.comp, Fvf, hamVF, hw, h2]
    rfl
  have hFd : DifferentiableAt ℂ (Fvf H₁) (axisPt t) :=
    (Fvf_holo hH).differentiableAt ((isOpen_Uset ρ s).mem_nhds (axis_mem hρ ht))
  have hchain : HasFDerivAt (Fvf H₁ ∘ ι) ((fderiv ℂ (Fvf H₁) (axisPt t)).comp ιL) 0 := by
    rw [← hι0] at hFd; rw [← hι0]; exact hFd.hasFDerivAt.comp 0 hι
  obtain ⟨hd1, e1⟩ := hasFDerivAt_d1 hH hρ ht 1
  obtain ⟨hd0, e0⟩ := hasFDerivAt_d1 hH hρ ht 0
  have hexp : HasFDerivAt (fun w =>
      ![fderiv ℂ (H₁ · t) w (eC 1), -fderiv ℂ (H₁ · t) w (eC 0), (1 : ℂ)])
      (ContinuousLinearMap.pi ![fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC 1)) 0,
        -fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC 0)) 0, 0]) 0 := by
    refine hasFDerivAt_pi.2 fun i => ?_
    fin_cases i
    · exact hd1
    · exact hd0.neg
    · exact hasFDerivAt_const _ _
  rw [hcomp] at hchain
  have hy' : y = ιL (wPart y) := by
    funext i; fin_cases i <;> simp [ιL, wPart, hy]
  have := congrArg (fun L => L (wPart y)) (hchain.unique hexp)
  simp only [ContinuousLinearMap.comp_apply] at this
  conv_lhs => rw [hy']
  rw [this]
  funext i; fin_cases i <;> simp [e1, e0, wPart]

end F

end ABC.S4.R2Aux
