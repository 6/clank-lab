import ABC.S4.PeriodMapAux2
import ABC.S4.PeriodMapAux3
import ABC.S4.PeriodMapAux4

/-! Assembly: the period map is the real trace of the holomorphic time-`2π` map. -/

open Set Metric Filter Topology
open scoped Real

noncomputable section

namespace ABC.S4.PeriodMapAux

open ABC ABC.S4

def ofRL : E 2 →L[ℝ] C2 :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

lemma ofRL_apply (x : E 2) : ofRL x = ofR x := rfl

def reL : C2 →L[ℝ] E 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
  (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

lemma reL_apply (w : C2) (i : Fin 2) : reL w i = (w i).re := rfl

def imL : C2 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => Complex.imCLM.comp (ContinuousLinearMap.proj i)

lemma imL_apply (w : C2) (i : Fin 2) : imL w i = (w i).im := rfl

lemma norm_ofR_le (x : E 2) : ‖ofR x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => by
    simpa [ofR] using PiLp.norm_apply_le x i

lemma norm_ext_le (w : C2) : ‖ext w 0‖ ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => by
    fin_cases i
    · exact norm_le_pi_norm w 0
    · exact norm_le_pi_norm w 1
    · simp [ext]

lemma ofRL_single (j : Fin 2) : ofRL (EuclideanSpace.single j 1) = Pi.single j 1 := by
  funext i; fin_cases i <;> fin_cases j <;> simp [ofRL_apply, ofR]

lemma extL_single (j : Fin 2) : extL (Pi.single j 1) = e3 (Fin.castSucc j) := by
  funext i; fin_cases i <;> fin_cases j <;> simp [extL, e3]

lemma hasDerivAt_ofReal_comp {n : ℕ} {f : ℂ → Cn n} {f' : Cn n} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s : ℝ => f s) f' t := by
  have := (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t Complex.ofRealCLM.hasDerivAt
  exact this.congr_deriv (by simp)

lemma hasDerivAt_ofReal (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

theorem period_map_main {H : C2 → ℂ → ℂ} {ρ s r : ℝ} {P : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hH : IsTPHam H ρ s)
    (h0 : ∀ t, hamVF (H · t) 0 = 0) (hP : IsPeriodMap H P r) (hr : 0 < r) :
    ContDiffAt ℝ ⊤ P 0 ∧ jdet P 0 = 1 := by
  have hpi : 0 < 2 * π := Real.two_pi_pos
  -- a tube around the equilibrium line `w = 0`
  set U' : Set (Cn 3) := {q | ‖pr q‖ < ρ / 2 ∧ |(q 2).im| < s / 2 ∧
    (q 2).re ∈ Ioo (-1) (2 * π + 1)}
  have hU'o : IsOpen U' := by
    have h1 : Continuous fun q : Cn 3 => ‖pr q‖ := by
      simp_rw [← prL_apply]; fun_prop
    refine (isOpen_lt h1 continuous_const).inter ((isOpen_lt
      (by fun_prop : Continuous fun q : Cn 3 => |(q 2).im|) continuous_const).inter
      (isOpen_Ioo.preimage (by fun_prop : Continuous fun q : Cn 3 => (q 2).re)))
  have hU'D : U' ⊆ Dom ρ s := fun q hq =>
    ⟨by simp only [polydisc, mem_ofPred_eq]; linarith [hq.1],
     by simp only [strip, mem_ofPred_eq]; linarith [hq.2.1]⟩
  have hFU' : DifferentiableOn ℂ (Fe H) U' := (Fe_diff hH).mono hU'D
  set γ₀ : ℝ → Cn 3 := fun t => ext 0 t
  have hγ₀ : ∀ t ∈ Icc 0 (2 * π),
      HasDerivWithinAt γ₀ (Fe H (γ₀ t)) (Icc 0 (2 * π)) t ∧ γ₀ t ∈ U' := by
    intro t ht
    have hst : (t : ℂ) ∈ strip s := by simp [strip, hs]
    refine ⟨?_, ?_⟩
    · rw [Fe_base hρ hH h0 hst]
      refine HasDerivAt.hasDerivWithinAt (hasDerivAt_pi.2 fun i => ?_)
      fin_cases i
      · simpa [γ₀, ext] using hasDerivAt_const t (0 : ℂ)
      · simpa [γ₀, ext] using hasDerivAt_const t (0 : ℂ)
      · simpa [γ₀, ext] using hasDerivAt_ofReal t
    · refine ⟨by simp [γ₀, pr_ext, hρ], by simp [γ₀, hs], ?_⟩
      simp only [γ₀, ext_two, Complex.ofReal_re, mem_Ioo]
      constructor <;> linarith [ht.1, ht.2]
  obtain ⟨s', hs', r', hr', φ, hφ, hφx⟩ := flow_complex_time hU'o hFU' hpi hγ₀
  have hγ00 : γ₀ 0 = 0 := by funext i; fin_cases i <;> simp [γ₀, ext]
  rw [hγ00] at hφ hφx
  -- the complex time domain
  set W : Set ℂ := {t | t.re ∈ Ioo (-s') (2 * π + s') ∧ |t.im| < s'}
  have hWo : IsOpen W := (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_lt (by fun_prop : Continuous fun t : ℂ => |t.im|) continuous_const)
  have hWc : Convex ℝ W := by
    have h1 : W = Complex.reLm ⁻¹' Ioo (-s') (2 * π + s') ∩ Complex.imLm ⁻¹' Ioo (-s') s' := by
      ext t; simp [W, abs_lt]
    rw [h1]
    exact ((convex_Ioo _ _).linear_preimage _).inter ((convex_Ioo _ _).linear_preimage _)
  have hreal : ∀ t ∈ Icc 0 (2 * π), (t : ℂ) ∈ W := fun t ht =>
    ⟨by simp only [Complex.ofReal_re, mem_Ioo]; constructor <;> linarith [ht.1, ht.2],
     by simp [hs']⟩
  have hW0 : (0 : ℂ) ∈ W := by simpa using hreal 0 ⟨le_rfl, hpi.le⟩
  set T2 : ℂ := ((2 * π : ℝ) : ℂ)
  have hW2 : T2 ∈ W := hreal _ ⟨hpi.le, le_rfl⟩
  have hφd : ∀ x ∈ ball (0 : Cn 3) r', ∀ t ∈ W, HasDerivAt (φ · x) (Fe H (φ t x)) t ∧ φ t x ∈ U' :=
    fun x hx t ht => (hφx x hx).2 t ht.1 ht.2
  have h0r : (0 : Cn 3) ∈ ball (0 : Cn 3) r' := mem_ball_self hr'
  -- Liouville
  set M := fderiv ℂ (φ T2) 0
  have hdet : (jmat M).det = 1 :=
    liouville hU'o hFU' (fun q hq => trace_Fe hH (hU'D hq)) hWo hWc.isPreconnected hW0 hr' hφ
      (fun x hx => (hφx x hx).1) hφd hW2
  -- the time component is `τ + t`
  have hthird : ∀ x ∈ ball (0 : Cn 3) r', φ T2 x 2 = x 2 + T2 := by
    intro x hx
    set g : ℂ → ℂ := fun t => φ t x 2 - t
    have hg : ∀ t ∈ W, HasDerivAt g 0 t := by
      intro t ht
      have h := (hasDerivAt_pi.1 (hφd x hx t ht).1 2).sub (hasDerivAt_id t)
      exact h.congr_deriv (by simp [Fe_two])
    have := hWo.is_const_of_deriv_eq_zero hWc.isPreconnected
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hg t ht).deriv) hW2 hW0
    simp only [g, (hφx x hx).1, sub_zero] at this
    linear_combination this
  have hφT : DifferentiableAt ℂ (φ T2) 0 := by
    have h1 : HasFDerivAt (fun y : Cn 3 => ((T2, y) : ℂ × Cn 3))
        (ContinuousLinearMap.inr ℂ ℂ (Cn 3)) 0 :=
      (hasFDerivAt_const T2 0).prodMk (hasFDerivAt_id 0)
    have hm : ((T2, 0) : ℂ × Cn 3) ∈ W ×ˢ ball (0 : Cn 3) r' := ⟨hW2, h0r⟩
    exact ((hφ _ hm).differentiableAt ((hWo.prod isOpen_ball).mem_nhds hm)).comp 0
      h1.differentiableAt
  have hM2 : ∀ v, M v 2 = v 2 := by
    intro v
    have hev : (fun y => φ T2 y 2) =ᶠ[𝓝 0] fun y => y 2 + T2 := by
      filter_upwards [isOpen_ball.mem_nhds h0r] with y hy
      exact hthird y hy
    have h1 : HasFDerivAt (fun y => φ T2 y 2) ((ContinuousLinearMap.proj 2).comp M) 0 :=
      (hasFDerivAt_apply (𝕜 := ℂ) 2 (φ T2 0)).comp 0 hφT.hasFDerivAt
    have h2 : HasFDerivAt (fun y : Cn 3 => y 2 + T2) (ContinuousLinearMap.proj 2) 0 :=
      (hasFDerivAt_apply (𝕜 := ℂ) 2 (0 : Cn 3)).add_const T2
    have := congrArg (fun L => L v) (h1.unique (h2.congr_of_eventuallyEq hev))
    simpa using this
  -- the holomorphic time-`2π` map on `ℂ²`
  set Φc : C2 → C2 := fun w => pr (φ T2 (ext w 0))
  have hext0 : ext 0 0 = (0 : Cn 3) := by funext i; fin_cases i <;> simp [ext]
  have hΦd : DifferentiableOn ℂ Φc (ball 0 r') := by
    intro w hw
    have hw' : ext w 0 ∈ ball (0 : Cn 3) r' :=
      mem_ball_zero_iff.2 ((norm_ext_le w).trans_lt (mem_ball_zero_iff.1 hw))
    have hm : ((T2, ext w 0) : ℂ × Cn 3) ∈ W ×ˢ ball (0 : Cn 3) r' := ⟨hW2, hw'⟩
    have h1 : DifferentiableAt ℂ (fun y => φ T2 y) (ext w 0) :=
      ((hφ _ hm).differentiableAt ((hWo.prod isOpen_ball).mem_nhds hm)).comp (ext w 0)
        ((differentiableAt_const T2).prodMk differentiableAt_id)
    refine DifferentiableAt.differentiableWithinAt ?_
    simp_rw [Φc, ← prL_apply]
    exact prL.differentiableAt.comp w (h1.comp w (hasFDerivAt_ext w 0).differentiableAt)
  have hΦa : AnalyticAt ℂ Φc 0 := analyticAt_of_differentiableOn isOpen_ball hΦd
    (mem_ball_self hr')
  -- uniqueness: `P` is the real trace of `Φc`
  have hPx : ∀ x : E 2, ‖x‖ < min r r' → ofR (P x) = Φc (ofR x) := by
    intro x hx
    obtain ⟨γ, hγs, hγ0, hγ2⟩ := hP x (hx.trans_le (min_le_left _ _))
    set X := ext (ofR x) 0
    have hX : X ∈ ball (0 : Cn 3) r' := mem_ball_zero_iff.2
      (((norm_ext_le _).trans (norm_ofR_le x)).trans_lt (hx.trans_le (min_le_right _ _)))
    set Γ : ℝ → Cn 3 := fun t => ext (γ t) t
    set Φ : ℝ → Cn 3 := fun t => φ t X
    have hγc : ContinuousOn γ (Icc 0 (2 * π)) := fun t ht => (hγs t ht).continuousWithinAt
    have hΓc : ContinuousOn Γ (Icc 0 (2 * π)) := by
      refine continuousOn_pi.2 fun i => ?_
      fin_cases i
      · simpa [Γ, ext] using continuousOn_pi.1 hγc 0
      · simpa [Γ, ext] using continuousOn_pi.1 hγc 1
      · simpa [Γ, ext] using Complex.continuous_ofReal.continuousOn
    have hΓd : ∀ t ∈ Ico 0 (2 * π), Γ t ∈ Dom ρ s →
        HasDerivWithinAt Γ (Fe H (Γ t)) (Ici t) t := by
      intro t ht hΓt
      have hγt := (hγs t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
      rw [hamVF_eq hH hΓt] at hγt
      refine hasDerivWithinAt_pi.2 fun i => ?_
      fin_cases i
      · simpa [Γ, ext, pr] using hasDerivWithinAt_pi.1 hγt 0
      · simpa [Γ, ext, pr] using hasDerivWithinAt_pi.1 hγt 1
      · simpa [Γ, ext, Fe_two] using
          (hasDerivAt_ofReal t).hasDerivWithinAt (s := Ici t)
    have hΦ' : ∀ t ∈ Icc 0 (2 * π), HasDerivAt Φ (Fe H (Φ t)) t := fun t ht =>
      hasDerivAt_ofReal_comp (hφd X hX t (hreal t ht)).1
    have key := solution_eq_flow (isOpen_Dom ρ s) (Fe_diff hH) hΓc hΓd
      (fun t ht => (hΦ' t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hΦ' t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hU'D (hφd X hX t (hreal t ht)).2)
      (by simp [Γ, Φ, X, hγ0, (hφx X hX).1]) (2 * π) ⟨hpi.le, le_rfl⟩
    rw [← hγ2, ← pr_ext (γ (2 * π)) ((2 * π : ℝ) : ℂ)]
    exact congrArg pr key
  -- real analyticity
  set Q : E 2 → E 2 := fun x => reL (Φc (ofRL x))
  have hPQ : P =ᶠ[𝓝 0] Q := by
    filter_upwards [ball_mem_nhds (0 : E 2) (lt_min hr hr')] with x hx
    ext i
    have := congrFun (hPx x (mem_ball_zero_iff.1 hx)) i
    rw [reL_apply, ofRL_apply, ← this]
    simp [ofR]
  have hΦa' : AnalyticAt ℝ Φc (ofRL 0) := by
    rw [map_zero]; exact hΦa.restrictScalars
  have hQa : AnalyticAt ℝ Q 0 :=
    reL.analyticAt _ |>.comp (hΦa'.comp (ofRL.analyticAt 0))
  refine ⟨hQa.contDiffAt.congr_of_eventuallyEq hPQ, ?_⟩
  -- the Jacobian
  set A := fderiv ℂ Φc 0
  have hA : HasFDerivAt Φc A (ofRL 0) := by rw [map_zero]; exact hΦa.differentiableAt.hasFDerivAt
  have hQd : HasFDerivAt Q (reL.comp ((A.restrictScalars ℝ).comp ofRL)) 0 :=
    reL.hasFDerivAt.comp 0 ((hA.restrictScalars ℝ).comp 0 ofRL.hasFDerivAt)
  -- imaginary parts vanish
  have hIm : ∀ i j : Fin 2, (A (Pi.single j 1) i).im = 0 := by
    intro i j
    set I' : E 2 → (Fin 2 → ℝ) := fun x => imL (Φc (ofRL x))
    have hI' : HasFDerivAt I' (imL.comp ((A.restrictScalars ℝ).comp ofRL)) 0 :=
      imL.hasFDerivAt.comp 0 ((hA.restrictScalars ℝ).comp 0 ofRL.hasFDerivAt)
    have hev : I' =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [ball_mem_nhds (0 : E 2) (lt_min hr hr')] with x hx
      funext k
      simp only [I', imL_apply, ofRL_apply, ← hPx x (mem_ball_zero_iff.1 hx)]
      simp [ofR]
    have := hI'.unique ((hasFDerivAt_const (0 : Fin 2 → ℝ) (0 : E 2)).congr_of_eventuallyEq hev)
    have h2 := congrFun (congrArg (fun L => L (EuclideanSpace.single j 1)) this) i
    simpa [imL_apply, ofRL_single] using h2
  -- the complex Jacobian is the `2×2` block of `M`
  have hAM : ∀ i j : Fin 2, A (Pi.single j 1) i = M (e3 (Fin.castSucc j)) (Fin.castSucc i) := by
    have hd : HasFDerivAt Φc (prL.comp (M.comp extL)) 0 := by
      have h1 : HasFDerivAt (φ T2) M (ext 0 0) := by rw [hext0]; exact hφT.hasFDerivAt
      have h2 := prL.hasFDerivAt.comp (0 : C2) (h1.comp (0 : C2) (hasFDerivAt_ext 0 0))
      convert h2 using 1
      funext w; simp [Φc, prL_apply]
    intro i j
    rw [show A = _ from hd.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, extL_single, prL_apply]
    fin_cases i <;> rfl
  have hdet2 : A (Pi.single 0 1) 0 * A (Pi.single 1 1) 1
      - A (Pi.single 1 1) 0 * A (Pi.single 0 1) 1 = 1 := by
    rw [hAM, hAM, hAM, hAM]
    rw [Matrix.det_fin_three] at hdet
    simp only [jmat, hM2] at hdet
    simpa [e3] using hdet
  -- the real Jacobian determinant
  have hfd : fderiv ℝ P 0 = reL.comp ((A.restrictScalars ℝ).comp ofRL) :=
    hPQ.fderiv_eq.trans hQd.fderiv
  unfold jdet
  rw [hfd, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', ofRL_single, reL_apply]
  have h := congrArg Complex.re hdet2
  simp only [Complex.sub_re, Complex.mul_re, hIm, mul_zero, sub_zero, Complex.one_re] at h
  exact h

end ABC.S4.PeriodMapAux
