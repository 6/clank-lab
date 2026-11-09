import ABC.S4.FlowComplex
import ABC.S4.PeriodMapAux1

/-! The extended autonomous field `(w, τ) ↦ (J∇H(·, τ)(w), 1)` on `ℂ³`. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.PeriodMapAux

open ABC ABC.S4

def pr (q : Cn 3) : C2 := ![q 0, q 1]

def ext (w : C2) (τ : ℂ) : Cn 3 := ![w 0, w 1, τ]

def Ht (H : C2 → ℂ → ℂ) (q : Cn 3) : ℂ := H (pr q) (q 2)

def Fe (H : C2 → ℂ → ℂ) (q : Cn 3) : Cn 3 :=
  ![fderiv ℂ (Ht H) q (Pi.single 1 1), -fderiv ℂ (Ht H) q (Pi.single 0 1), 1]

def Dom (ρ s : ℝ) : Set (Cn 3) := {q | pr q ∈ polydisc ρ ∧ q 2 ∈ strip s}

def prL : Cn 3 →L[ℂ] C2 := ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
  ContinuousLinearMap.proj 1]

def extL : C2 →L[ℂ] Cn 3 := ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
  ContinuousLinearMap.proj 1, 0]

lemma prL_apply (q : Cn 3) : prL q = pr q := by
  funext i; fin_cases i <;> rfl

lemma extL_apply (v : C2) : extL v = ext v 0 := by
  funext i; fin_cases i <;> rfl

lemma pr_ext (w : C2) (τ : ℂ) : pr (ext w τ) = w := by
  funext i; fin_cases i <;> rfl

@[simp] lemma ext_two (w : C2) (τ : ℂ) : ext w τ 2 = τ := rfl

lemma Fe_zero (H : C2 → ℂ → ℂ) (q : Cn 3) : Fe H q 0 = fderiv ℂ (Ht H) q (Pi.single 1 1) := rfl
lemma Fe_one (H : C2 → ℂ → ℂ) (q : Cn 3) : Fe H q 1 = -fderiv ℂ (Ht H) q (Pi.single 0 1) := rfl
lemma Fe_two (H : C2 → ℂ → ℂ) (q : Cn 3) : Fe H q 2 = 1 := rfl

lemma ext_eq_add (w : C2) (τ : ℂ) : ext w τ = extL w + ext 0 τ := by
  funext i; fin_cases i <;> simp [extL, ext]

lemma hasFDerivAt_ext (w : C2) (τ : ℂ) : HasFDerivAt (fun w => ext w τ) extL w := by
  have : (fun w => ext w τ) = fun w => extL w + ext 0 τ := funext fun w => ext_eq_add w τ
  rw [this]
  exact extL.hasFDerivAt.add_const _

lemma isOpen_Dom (ρ s : ℝ) : IsOpen (Dom ρ s) := by
  have h1 : Continuous fun q : Cn 3 => ‖pr q‖ := by
    simp_rw [← prL_apply]; fun_prop
  exact (isOpen_lt h1 continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous fun q : Cn 3 => |(q 2).im|) continuous_const)

lemma Ht_diff {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) :
    DifferentiableOn ℂ (Ht H) (Dom ρ s) := by
  have hg : Differentiable ℂ fun q : Cn 3 => (prL q, q 2) := by fun_prop
  have hm : MapsTo (fun q : Cn 3 => (prL q, q 2)) (Dom ρ s) (polydisc ρ ×ˢ strip s) :=
    fun q hq => by simp only [prL_apply]; exact ⟨hq.1, hq.2⟩
  have := hH.holo.comp hg.differentiableOn hm
  convert this using 1
  funext q
  simp [Ht, prL_apply]

lemma Ht_analytic {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {q : Cn 3}
    (hq : q ∈ Dom ρ s) : AnalyticAt ℂ (Ht H) q :=
  analyticAt_of_differentiableOn (isOpen_Dom ρ s) (Ht_diff hH) hq

lemma Fe_diff {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) :
    DifferentiableOn ℂ (Fe H) (Dom ρ s) := by
  have hD := differentiableOn_fderiv (isOpen_Dom ρ s) (Ht_diff hH)
  refine differentiableOn_pi.2 fun i => ?_
  fin_cases i
  · exact hD.clm_apply (differentiableOn_const _)
  · exact (hD.clm_apply (differentiableOn_const _)).neg
  · exact differentiableOn_const _

lemma hamVF_eq {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {w : C2} {τ : ℂ}
    (hq : ext w τ ∈ Dom ρ s) : hamVF (fun w => H w τ) w = pr (Fe H (ext w τ)) := by
  have hfun : (fun w' => H w' τ) = Ht H ∘ (fun w' => ext w' τ) :=
    funext fun w' => by simp [Ht, pr_ext]
  have hd : HasFDerivAt (fun w' => H w' τ) ((fderiv ℂ (Ht H) (ext w τ)).comp extL) w := by
    rw [hfun]
    exact ((Ht_diff hH _ hq).differentiableAt ((isOpen_Dom ρ s).mem_nhds hq)).hasFDerivAt.comp w
      (hasFDerivAt_ext w τ)
  have e1 : extL (Pi.single 1 1) = (Pi.single 1 1 : Cn 3) := by
    funext i; fin_cases i <;> simp [extL]
  have e0 : extL (Pi.single 0 1) = (Pi.single 0 1 : Cn 3) := by
    funext i; fin_cases i <;> simp [extL]
  unfold hamVF
  rw [hd.fderiv]
  funext i
  fin_cases i
  · simp [e1, pr, Fe]
  · simp [e0, pr, Fe]

lemma Fe_base {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hρ : 0 < ρ) (hH : IsTPHam H ρ s)
    (h0 : ∀ t, hamVF (H · t) 0 = 0) {τ : ℂ} (hτ : τ ∈ strip s) :
    Fe H (ext 0 τ) = ![0, 0, 1] := by
  have hq : ext 0 τ ∈ Dom ρ s := ⟨by simp [pr_ext, polydisc, hρ], hτ⟩
  have h := hamVF_eq hH hq
  rw [h0 τ] at h
  funext i
  fin_cases i
  · have := congrFun h 0; simp [pr] at this; simp [← this]
  · have := congrFun h 1; simp [pr] at this; simp [← this]
  · rfl

lemma fderiv_Fe_apply {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {q : Cn 3}
    (hq : q ∈ Dom ρ s) (v : Cn 3) :
    fderiv ℂ (Fe H) q v = ![fderiv ℂ (fderiv ℂ (Ht H)) q v (Pi.single 1 1),
      -fderiv ℂ (fderiv ℂ (Ht H)) q v (Pi.single 0 1), 0] := by
  have hn := (isOpen_Dom ρ s).mem_nhds hq
  have hD : DifferentiableAt ℂ (fderiv ℂ (Ht H)) q :=
    (differentiableOn_fderiv (isOpen_Dom ρ s) (Ht_diff hH) q hq).differentiableAt hn
  have hc : ∀ i, DifferentiableAt ℂ (fun q => Fe H q i) q := fun i =>
    ((differentiableOn_pi.1 (Fe_diff hH) i) q hq).differentiableAt hn
  rw [fderiv_pi hc]
  funext i
  fin_cases i
  · simp only [ContinuousLinearMap.pi_apply]
    show fderiv ℂ (fun q => fderiv ℂ (Ht H) q (Pi.single 1 1)) q v = _
    rw [fderiv_clm_apply hD (differentiableAt_const _)]
    simp
  · simp only [ContinuousLinearMap.pi_apply]
    show fderiv ℂ (fun q => -fderiv ℂ (Ht H) q (Pi.single 0 1)) q v = _
    rw [fderiv_fun_neg, fderiv_clm_apply hD (differentiableAt_const _)]
    simp
  · simp only [ContinuousLinearMap.pi_apply]
    show fderiv ℂ (fun _ => (1 : ℂ)) q v = _
    simp

lemma trace_Fe {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {q : Cn 3}
    (hq : q ∈ Dom ρ s) :
    fderiv ℂ (Fe H) q (Pi.single 0 1) 0 + fderiv ℂ (Fe H) q (Pi.single 1 1) 1
      + fderiv ℂ (Fe H) q (Pi.single 2 1) 2 = 0 := by
  have hs := ((Ht_analytic hH hq).contDiffAt (n := ⊤)).isSymmSndFDerivAt_of_omega
  rw [fderiv_Fe_apply hH hq, fderiv_Fe_apply hH hq, fderiv_Fe_apply hH hq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [hs (Pi.single 0 1) (Pi.single 1 1)]
  ring

end ABC.S4.PeriodMapAux
