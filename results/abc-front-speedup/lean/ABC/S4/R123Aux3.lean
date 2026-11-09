import ABC.S4.R123Aux2

/-! R123 helpers: real/complex coordinates, local analytic inverses, chart composition and the
trace of a conjugated map. -/

open Set Metric Filter Topology Asymptotics

noncomputable section

namespace ABC.S4.R123Aux

open ABC ABC.S4

/-- `ofR` as a real-linear map. -/
def ofRL : E 2 →L[ℝ] C2 :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

theorem ofRL_apply (x : E 2) : ofRL x = ofR x := rfl

/-- Real parts, as a point of `E 2`. -/
def reL : C2 →L[ℝ] E 2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

theorem reL_apply (w : C2) (i : Fin 2) : reL w i = (w i).re := rfl

theorem reL_ofR (x : E 2) : reL (ofR x) = x := by
  ext i; simp [reL_apply, ofR]

theorem ofR_reL {w : C2} (h : ∀ i, (w i).im = 0) : ofR (reL w) = w := by
  funext i
  apply Complex.ext <;> simp [ofR, reL_apply, h i]

theorem norm_ofR_le (x : E 2) : ‖ofR x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simp only [ofR, Complex.norm_real]
  exact PiLp.norm_apply_le x i

theorem ofR_injective : Function.Injective ofR := by
  intro x y h
  rw [← reL_ofR x, h, reL_ofR]

theorem ofR_zero : ofR 0 = 0 := by funext i; simp [ofR]

/-- A function `O(‖w‖²)` at `0` has derivative `0` there. -/
theorem hasFDerivAt_zero_of_sq_bound {f : C2 → ℂ} {C r : ℝ} (hr : 0 < r)
    (hf : ∀ w : C2, ‖w‖ < r → ‖f w‖ ≤ C * ‖w‖ ^ 2) : HasFDerivAt f (0 : C2 →L[ℂ] ℂ) 0 := by
  have hf0 : f 0 = 0 := by
    have := hf 0 (by simpa using hr)
    simpa using this
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, hf0, sub_zero, zero_apply]
  have h1 : f =O[𝓝 0] (fun w : C2 => ‖w‖ ^ 2) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [ball_mem_nhds 0 hr] with w hw
    rw [mem_ball_zero_iff] at hw
    simpa [norm_pow] using hf w hw
  exact h1.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

theorem hamVF_zero_of_fderiv {f : C2 → ℂ} (h : fderiv ℂ f 0 = 0) : hamVF f 0 = 0 := by
  funext i; fin_cases i <;> simp [hamVF, h]

theorem norm_sq_add_sq_le (w : C2) : ‖w 0 ^ 2 + w 1 ^ 2‖ ≤ 2 * ‖w‖ ^ 2 := by
  have h0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have h1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  calc ‖w 0 ^ 2 + w 1 ^ 2‖ ≤ ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
        refine (norm_add_le _ _).trans ?_; simp [norm_pow]
    _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by gcongr
    _ = 2 * ‖w‖ ^ 2 := by ring

theorem Kbnf_sq_bound {ν b C ρ s : ℝ} {R : C2 → ℂ → ℂ} (hR : Bound R ρ s C 5) {t : ℂ}
    (ht : t ∈ strip s) (w : C2) (hw : ‖w‖ < min ρ 1) :
    ‖Kbnf ν b R w t‖ ≤ (|ν| + |b| + |C|) * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ ≤ 1 := (hw.trans_le (min_le_right _ _)).le
  have hwρ : w ∈ polydisc ρ := hw.trans_le (min_le_left _ _)
  set a := ‖w‖
  have ha : 0 ≤ a := norm_nonneg _
  have hX := norm_sq_add_sq_le w
  have hRw := hR w hwρ t ht
  have e1 : ‖(ν : ℂ) / 2 * (w 0 ^ 2 + w 1 ^ 2)‖ ≤ |ν| * a ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    nlinarith [abs_nonneg ν]
  have e2 : ‖(b : ℂ) / 4 * (w 0 ^ 2 + w 1 ^ 2) ^ 2‖ ≤ |b| * a ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, norm_pow]
    have hX2 : ‖w 0 ^ 2 + w 1 ^ 2‖ ^ 2 ≤ 4 * a ^ 2 := by
      have : ‖w 0 ^ 2 + w 1 ^ 2‖ ^ 2 ≤ (2 * a ^ 2) ^ 2 := by gcongr
      nlinarith [pow_le_one₀ ha hw1 (n := 2)]
    nlinarith [abs_nonneg b]
  have e3 : ‖R w t‖ ≤ |C| * a ^ 2 := by
    refine hRw.trans ?_
    have : a ^ 5 ≤ a ^ 2 := pow_le_pow_of_le_one ha hw1 (by norm_num)
    nlinarith [le_abs_self C, abs_nonneg C, pow_nonneg ha 5, pow_nonneg ha 2]
  calc ‖Kbnf ν b R w t‖ ≤ ‖(ν : ℂ) / 2 * (w 0 ^ 2 + w 1 ^ 2)‖ +
        ‖(b : ℂ) / 4 * (w 0 ^ 2 + w 1 ^ 2) ^ 2‖ + ‖R w t‖ := by
        unfold Kbnf; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by nlinarith

set_option synthInstance.maxHeartbeats 400000 in
/-- An analytic map with injective derivative at `0` is a local analytic diffeomorphism. -/
theorem exists_localHomeo {L : E 2 → E 2} {r₀ : ℝ} (hL : AnalyticOnNhd ℝ L (ball 0 r₀))
    (hr₀ : 0 < r₀) (hinj : Function.Injective (fderiv ℝ L 0)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Lh : OpenPartialHomeomorph (E 2) (E 2), ⇑Lh = L ∧ (0 : E 2) ∈ Lh.source ∧
      Lh.source ⊆ ball 0 (min κ r₀) ∧ AnalyticOnNhd ℝ Lh Lh.source ∧
      AnalyticOnNhd ℝ Lh.symm Lh.target := by
  have h0 : (0 : E 2) ∈ ball (0 : E 2) r₀ := mem_ball_self hr₀
  set A := fderiv ℝ L 0
  let Ae : E 2 ≃L[ℝ] E 2 :=
    (LinearEquiv.ofInjectiveEndo (A : E 2 →ₗ[ℝ] E 2) hinj).toContinuousLinearEquiv
  have hAe : (Ae : E 2 →L[ℝ] E 2) = A := by ext x; rfl
  have hstrict : HasStrictFDerivAt L (Ae : E 2 →L[ℝ] E 2) 0 := by
    rw [hAe]; exact (hL 0 h0).hasStrictFDerivAt
  set L0 := hstrict.toOpenPartialHomeomorph L
  have hball : ball (0 : E 2) (min κ r₀) ⊆ ball 0 r₀ := ball_subset_ball (min_le_right _ _)
  have hfc : ContinuousOn (fderiv ℝ L) (ball 0 (min κ r₀)) :=
    ((hL.fderiv).continuousOn).mono hball
  set D := ball (0 : E 2) (min κ r₀) ∩ (fderiv ℝ L) ⁻¹' {u | IsUnit u}
  have hD : IsOpen D := hfc.isOpen_inter_preimage isOpen_ball Units.isOpen
  have h0D : (0 : E 2) ∈ D := by
    refine ⟨mem_ball_self (lt_min hκ hr₀), ?_⟩
    show IsUnit A
    rw [← hAe]
    exact ⟨Ae.toUnit, rfl⟩
  set Lh := L0.restrOpen D hD
  have hcoe : ⇑Lh = L := rfl
  have hsrc : Lh.source = L0.source ∩ D := L0.restrOpen_source D hD
  have hsub : Lh.source ⊆ ball 0 (min κ r₀) := by rw [hsrc]; exact fun x hx => hx.2.1
  refine ⟨Lh, hcoe, ?_, hsub, ?_, ?_⟩
  · rw [hsrc]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, h0D⟩
  · intro x hx
    rw [hcoe]; exact hL x (hball (hsub hx))
  · intro y hy
    have hx := Lh.map_target hy
    have hxD : Lh.symm y ∈ D := by rw [hsrc] at hx; exact hx.2
    obtain ⟨u, hu⟩ := hxD.2
    refine Lh.analyticAt_symm hy (i := ContinuousLinearEquiv.unitsEquiv ℝ (E 2) u) ?_ ?_
    · rw [hcoe]; exact hL _ (hball (hsub hx))
    · rw [hcoe, ← hu]; rfl

theorem analyticOnNhd_of_isChart {h : OpenPartialHomeomorph (E 2) (E 2)} {p : E 2} {r : ℝ}
    (hc : IsChart h p r) : AnalyticOnNhd ℝ h h.source ∧ AnalyticOnNhd ℝ h.symm h.target :=
  ⟨fun _x hx => (hc.2.2.2.1.contDiffAt (h.open_source.mem_nhds hx)).analyticAt,
    fun _y hy => (hc.2.2.2.2.contDiffAt (h.open_target.mem_nhds hy)).analyticAt⟩

theorem isChart_trans {h₁ Lh : OpenPartialHomeomorph (E 2) (E 2)} {p : E 2} {ρ₁ ρ : ℝ}
    (hch : IsChart h₁ p ρ₁) (hL0 : Lh 0 = 0) (hLa : AnalyticOnNhd ℝ Lh Lh.source)
    (hLs : AnalyticOnNhd ℝ Lh.symm Lh.target) (hball : ball 0 ρ ⊆ (Lh.trans h₁).source) :
    IsChart (Lh.trans h₁) p ρ := by
  obtain ⟨ha, hs⟩ := analyticOnNhd_of_isChart hch
  have hA : AnalyticOnNhd ℝ (Lh.trans h₁) (Lh.trans h₁).source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    rw [OpenPartialHomeomorph.coe_trans]
    exact (ha _ hx.2).comp (hLa x hx.1)
  have hS : AnalyticOnNhd ℝ (Lh.trans h₁).symm (Lh.trans h₁).target := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact (hLs _ hy.2).comp (hs y hy.1)
  refine ⟨?_, hball, (Lh.trans h₁).open_source, hA.contDiffOn
    (Lh.trans h₁).open_source.uniqueDiffOn, hS.contDiffOn (Lh.trans h₁).open_target.uniqueDiffOn⟩
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hL0]
  exact hch.1

/-- Trace is preserved by the chart conjugacy. -/
theorem jtr_eq_of_conj {h₁ : OpenPartialHomeomorph (E 2) (E 2)} {p : E 2} {ρ₁ : ℝ}
    (hch : IsChart h₁ p ρ₁) (hρ₁ : 0 < ρ₁) {P₁ : E 2 → E 2} (hP0 : P₁ 0 = 0)
    (hPd : DifferentiableAt ℝ P₁ 0)
    (hconj : ∀ x : E 2, ‖x‖ < ρ₁ → retMap (h₁ x) = h₁ (P₁ x)) {M : E 2 →L[ℝ] E 2}
    (hM : HasFDerivAt retMap M p) :
    jtr P₁ 0 = LinearMap.trace ℝ (E 2) (M : E 2 →ₗ[ℝ] E 2) := by
  obtain ⟨ha, hs⟩ := analyticOnNhd_of_isChart hch
  have h0s : (0 : E 2) ∈ h₁.source := hch.2.1 (mem_ball_self hρ₁)
  have hp : h₁ 0 = p := hch.1
  have hpt : p ∈ h₁.target := hp ▸ h₁.map_source h0s
  have hsp : h₁.symm p = 0 := by rw [← hp]; exact h₁.left_inv h0s
  set A := fderiv ℝ h₁ 0
  set B := fderiv ℝ h₁.symm p
  have hA : HasFDerivAt h₁ A 0 := (ha 0 h0s).differentiableAt.hasFDerivAt
  have hB : HasFDerivAt h₁.symm B p := (hs p hpt).differentiableAt.hasFDerivAt
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (E 2) := by
    have h1 : HasFDerivAt (h₁.symm ∘ h₁) (B.comp A) 0 := by
      have hB' : HasFDerivAt h₁.symm B (h₁ 0) := by rw [hp]; exact hB
      exact hB'.comp 0 hA
    have h2 : HasFDerivAt (h₁.symm ∘ h₁) (ContinuousLinearMap.id ℝ (E 2)) 0 :=
      (hasFDerivAt_id 0).congr_of_eventuallyEq (h₁.eventually_left_inverse h0s)
    exact h1.unique h2
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (E 2) := by
    have h1 : HasFDerivAt (h₁ ∘ h₁.symm) (A.comp B) p := by
      have hA' : HasFDerivAt h₁ A (h₁.symm p) := by rw [hsp]; exact hA
      exact hA'.comp p hB
    have h2 : HasFDerivAt (h₁ ∘ h₁.symm) (ContinuousLinearMap.id ℝ (E 2)) p :=
      (hasFDerivAt_id p).congr_of_eventuallyEq (h₁.eventually_right_inverse hpt)
    exact h1.unique h2
  set D := fderiv ℝ P₁ 0
  have hMA : M.comp A = A.comp D := by
    have h1 : HasFDerivAt (retMap ∘ h₁) (M.comp A) 0 := by
      have hM' : HasFDerivAt retMap M (h₁ 0) := by rw [hp]; exact hM
      exact hM'.comp 0 hA
    have h2 : HasFDerivAt (h₁ ∘ P₁) (A.comp D) 0 := by
      have hA' : HasFDerivAt h₁ A (P₁ 0) := by rw [hP0]; exact hA
      exact hA'.comp 0 hPd.hasFDerivAt
    have heq : retMap ∘ h₁ =ᶠ[𝓝 0] h₁ ∘ P₁ := by
      filter_upwards [ball_mem_nhds (0 : E 2) hρ₁] with x hx
      exact hconj x (by simpa using hx)
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hD : D = B.comp (M.comp A) := by
    rw [hMA, ← ContinuousLinearMap.comp_assoc, hBA, ContinuousLinearMap.id_comp]
  let e : E 2 ≃L[ℝ] E 2 := ContinuousLinearEquiv.equivOfInverse B A
    (fun x => by simpa using congrArg (fun f => f x) hAB)
    (fun x => by simpa using congrArg (fun f => f x) hBA)
  have hconjD : (D : E 2 →ₗ[ℝ] E 2) = e.toLinearEquiv.conj (M : E 2 →ₗ[ℝ] E 2) := by
    apply LinearMap.ext; intro x
    rw [hD]; rfl
  unfold jtr
  rw [hconjD, LinearMap.trace_conj']

/-- The period map fixes `0` when `0` is an equilibrium. -/
theorem periodMap_zero {H : C2 → ℂ → ℂ} {ρ s : ℝ} {P : E 2 → E 2} (hH : IsTPHam H ρ s)
    (hs : 0 < s) (hρ : 0 < ρ) (h0 : ∀ t : ℝ, hamVF (fun w => H w t) 0 = 0)
    (hP : IsPeriodMap H P ρ) : P 0 = 0 := by
  obtain ⟨γ, hγ, hγ0, hγT⟩ := hP 0 (by simpa using hρ)
  have hz : Solves H (fun _ => 0) 0 (2 * Real.pi) := by
    intro t _
    rw [h0]
    exact hasDerivWithinAt_const _ _ _
  have := solves_unique hH hs hz hγ (by rw [hγ0, ofR_zero])
    (fun t _ => by simpa [polydisc] using hρ)
    (show 2 * Real.pi ∈ Icc 0 (2 * Real.pi) from ⟨by positivity, le_rfl⟩)
  apply ofR_injective
  rw [← hγT, ← this, ofR_zero]

end ABC.S4.R123Aux
