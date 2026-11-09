import ABC.S4.PeriodMap
import ABC.S4.R123Aux1

/-! R123 helpers: time-dependent Hamiltonian flows as autonomous holomorphic flows in `Cn 3`
(time as the first coordinate); existence near the zero solution, uniqueness while one solution
stays in the polydisc, and uniform smallness on `[0, T]`. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.R123Aux

open ABC ABC.S4

/-- Time-extended field `(τ, w) ↦ (1, J∇_w H(w, τ))`. -/
def augH (H : C2 → ℂ → ℂ) (v : Cn 3) : Cn 3 :=
  Fin.cons 1 (hamVF (fun w => H w (v 0)) (Fin.tail v))

/-- Time-extended curve `t ↦ (t, γ t)`. -/
def augC (γ : ℝ → C2) (t : ℝ) : Cn 3 := Fin.cons (t : ℂ) (γ t)

/-- Domain `strip × polydisc` in `Cn 3`. -/
def augW (ρ s : ℝ) : Set (Cn 3) := {v | v 0 ∈ strip s ∧ Fin.tail v ∈ polydisc ρ}

theorem continuous_tail : Continuous (fun v : Cn 3 => (Fin.tail v : C2)) :=
  continuous_pi fun i => continuous_apply i.succ

theorem isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem isOpen_polydisc (ρ : ℝ) : IsOpen (polydisc ρ) := by
  have : polydisc ρ = ball (0 : C2) ρ := by ext; simp [polydisc]
  rw [this]; exact isOpen_ball

theorem isOpen_augW (ρ s : ℝ) : IsOpen (augW ρ s) := by
  have h1 : IsOpen ((fun v : Cn 3 => v 0) ⁻¹' strip s) :=
    (isOpen_strip s).preimage (continuous_apply 0)
  exact h1.inter ((isOpen_polydisc ρ).preimage continuous_tail)

theorem real_mem_strip {s : ℝ} (hs : 0 < s) (t : ℝ) : (t : ℂ) ∈ strip s := by
  simp [strip, hs]

theorem augC_mem {γ : ℝ → C2} {ρ s : ℝ} (hs : 0 < s) {t : ℝ} (h : γ t ∈ polydisc ρ) :
    augC γ t ∈ augW ρ s := by
  refine ⟨?_, ?_⟩
  · simpa [augC] using real_mem_strip hs t
  · simpa [augC] using h

/-- Partial derivative in `w` of a jointly holomorphic function. -/
theorem fderiv_partial {H : C2 → ℂ → ℂ} {O : Set (C2 × ℂ)} (hO : IsOpen O)
    (hH : DifferentiableOn ℂ (fun q : C2 × ℂ => H q.1 q.2) O) {q : C2 × ℂ} (hq : q ∈ O) :
    fderiv ℂ (fun w => H w q.2) q.1 =
      (fderiv ℂ (fun q : C2 × ℂ => H q.1 q.2) q).comp (ContinuousLinearMap.inl ℂ C2 ℂ) := by
  have hd : DifferentiableAt ℂ (fun q : C2 × ℂ => H q.1 q.2) q :=
    hH.differentiableAt (hO.mem_nhds hq)
  have hl : HasFDerivAt (fun w : C2 => (w, q.2)) (ContinuousLinearMap.inl ℂ C2 ℂ) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have : HasFDerivAt (fun w => H w q.2)
      ((fderiv ℂ (fun q : C2 × ℂ => H q.1 q.2) q).comp (ContinuousLinearMap.inl ℂ C2 ℂ)) q.1 := by
    have h := hd.hasFDerivAt
    exact h.comp q.1 hl
  exact this.fderiv

/-- The partial derivative `∂_w H(w, τ) u` is jointly holomorphic. -/
theorem differentiableOn_partial {H : C2 → ℂ → ℂ} {ρ s : ℝ}
    (hH : DifferentiableOn ℂ (fun q : C2 × ℂ => H q.1 q.2) (polydisc ρ ×ˢ strip s)) (u : C2) :
    DifferentiableOn ℂ (fun v : Cn 3 => fderiv ℂ (fun w => H w (v 0)) (Fin.tail v) u)
      (augW ρ s) := by
  have hO : IsOpen (polydisc ρ ×ˢ strip s) := (isOpen_polydisc ρ).prod (isOpen_strip s)
  set G := fun q : C2 × ℂ => H q.1 q.2
  set π : Cn 3 → C2 × ℂ := fun v => (Fin.tail v, v 0)
  have hπ : Differentiable ℂ π := by
    refine Differentiable.prodMk ?_ (differentiable_apply 0)
    exact differentiable_pi.2 fun i => differentiable_apply i.succ
  have hD : DifferentiableOn ℂ (fun q => fderiv ℂ G q (u, 0)) (polydisc ρ ×ˢ strip s) :=
    fun q hq => (HoloDeriv.differentiableAt_fderiv_apply hO hH hq _).differentiableWithinAt
  have h1 : DifferentiableOn ℂ (fun v => fderiv ℂ G (π v) (u, 0)) (augW ρ s) :=
    hD.comp hπ.differentiableOn (fun v hv => ⟨hv.2, hv.1⟩)
  refine h1.congr fun v hv => ?_
  have hq : π v ∈ polydisc ρ ×ˢ strip s := ⟨hv.2, hv.1⟩
  have := fderiv_partial hO hH hq
  simp only [π] at this
  rw [this]
  simp [G, π]

theorem differentiableOn_augH {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) :
    DifferentiableOn ℂ (augH H) (augW ρ s) := by
  refine differentiableOn_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [augH, Fin.cons_zero]
    exact differentiableOn_const _
  · simp only [augH, Fin.cons_succ]
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [hamVF] using differentiableOn_partial hH.holo (Pi.single 1 1)
    · have hk : k = 0 := Subsingleton.elim _ _
      subst hk
      simpa [hamVF] using (differentiableOn_partial hH.holo (Pi.single 0 1)).neg

theorem hasDerivWithinAt_augC {γ : ℝ → C2} {S : Set ℝ} {t : ℝ} {d : C2}
    (h : HasDerivWithinAt γ d S t) : HasDerivWithinAt (augC γ) (Fin.cons 1 d) S t := by
  refine hasDerivWithinAt_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [augC, Fin.cons_zero]
    exact (hasDerivAt_id t).ofReal_comp.hasDerivWithinAt
  · simp only [augC, Fin.cons_succ]
    exact (hasDerivWithinAt_pi.1 h) j

theorem augH_augC (H : C2 → ℂ → ℂ) (γ : ℝ → C2) (t : ℝ) :
    augH H (augC γ t) = Fin.cons 1 (hamVF (fun w => H w t) (γ t)) := by
  simp [augH, augC]

theorem solves_aug {H : C2 → ℂ → ℂ} {γ : ℝ → C2} {a b : ℝ} (h : Solves H γ a b) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (augC γ) (augH H (augC γ t)) (Icc a b) t := by
  intro t ht
  rw [augH_augC]
  exact hasDerivWithinAt_augC (h t ht)

theorem tail_augC (γ : ℝ → C2) (t : ℝ) : Fin.tail (augC γ t) = γ t := by simp [augC]

/-- Uniqueness for a time-periodic holomorphic Hamiltonian, while one solution stays inside. -/
theorem solves_unique {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) (hs : 0 < s)
    {f g : ℝ → C2} {a b : ℝ} (hf : Solves H f a b) (hg : Solves H g a b) (h0 : f a = g a)
    (hin : ∀ t ∈ Icc a b, f t ∈ polydisc ρ) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  rcases lt_or_ge b a with hab | hab
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hab)
  have hcl : IsClosed ({t | f t = g t} ∩ Icc a b) := by
    have := (hfc.prodMk hgc).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_diagonal (X := C2))
    convert this using 1
    ext t; simp [and_comm]
  have key := hcl.Icc_subset_of_forall_mem_nhdsWithin (show a ∈ {t | f t = g t} from h0) ?_
  · exact fun t ht => key ht
  rintro x ⟨hx, hxI⟩
  have hxI' : x ∈ Icc a b := Ico_subset_Icc_self hxI
  have hgx : g x ∈ polydisc ρ := by rw [← (hx : f x = g x)]; exact hin x hxI'
  have hev : ∀ᶠ t in 𝓝[Icc a b] x, g t ∈ polydisc ρ :=
    hgc x hxI' ((isOpen_polydisc ρ).mem_nhds hgx)
  obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set b' := min b (x + ε / 2)
  have hxb' : x < b' := lt_min hxI.2 (by linarith)
  have hsub : Icc x b' ⊆ Icc a b := Icc_subset_Icc hxI'.1 (min_le_left _ _)
  have hgin : ∀ t ∈ Icc x b', g t ∈ polydisc ρ := by
    intro t ht
    refine hεg ⟨?_, hsub ht⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [ht.1]
    · linarith [ht.2, min_le_right b (x + ε / 2)]
  have huniq := FlowComplexAux.odeUniq (isOpen_augW ρ s) (differentiableOn_augH hH)
    (f := augC f) (g := augC g) (a := x) (b := b')
    (fun t ht => ⟨(solves_aug hf t (hsub ht)).mono hsub, augC_mem hs (hin t (hsub ht))⟩)
    (fun t ht => ⟨(solves_aug hg t (hsub ht)).mono hsub, augC_mem hs (hgin t ht)⟩)
    (by have hx' : f x = g x := hx; simp only [augC, hx'])
  filter_upwards [Icc_mem_nhdsGT hxb'] with t ht
  have := congrArg Fin.tail (huniq ht)
  simpa [tail_augC] using this

/-- Solutions from small initial data exist on `[0, T]` and stay in the polydisc. -/
theorem exists_solves {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) (hs : 0 < s)
    (hρ : 0 < ρ) (h0 : ∀ t : ℝ, hamVF (fun w => H w t) 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    ∃ r > 0, ∀ w₀ : C2, ‖w₀‖ < r → ∃ γ : ℝ → C2, Solves H γ 0 T ∧ γ 0 = w₀ ∧
      ∀ t ∈ Icc 0 T, γ t ∈ polydisc ρ := by
  have hzero : ∀ t ∈ Icc 0 T, HasDerivWithinAt (augC (fun _ => 0)) (augH H (augC (fun _ => 0) t))
      (Icc 0 T) t ∧ augC (fun _ => 0) t ∈ augW ρ s := by
    intro t _
    refine ⟨?_, augC_mem hs (by simp [polydisc, hρ])⟩
    rw [augH_augC, h0]
    exact hasDerivWithinAt_augC (hasDerivWithinAt_const _ _ _)
  obtain ⟨r, hr, φ, -, hφ⟩ := flow_holo (isOpen_augW ρ s) (differentiableOn_augH hH) hT hzero
  refine ⟨r, hr, fun w₀ hw₀ => ?_⟩
  set v : Cn 3 := Fin.cons 0 w₀
  have hv : v ∈ ball (augC (fun _ => 0) 0) r := by
    rw [mem_ball, dist_pi_lt_iff hr]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [v, augC, hr]
    · simp only [v, augC, Fin.cons_succ, Pi.zero_apply, dist_zero_right]
      exact lt_of_le_of_lt (norm_le_pi_norm w₀ j) hw₀
  obtain ⟨hφ0, hφt⟩ := hφ v hv
  -- the time coordinate is `t`
  have htime : ∀ t ∈ Icc 0 T, φ t v 0 = t := by
    have hc : ContinuousOn (fun t => φ t v 0 - (t : ℂ)) (Icc 0 T) := by
      intro t ht
      exact (((continuousWithinAt_pi.1 (hφt t ht).1.continuousWithinAt) 0).sub
        Complex.continuous_ofReal.continuousWithinAt)
    have hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => φ t v 0 - (t : ℂ)) 0 (Ici t) t := by
      intro t ht
      have h1 := (hasDerivWithinAt_pi.1 (hφt t (Ico_subset_Icc_self ht)).1) 0
      simp only [augH, Fin.cons_zero] at h1
      have h2 := h1.sub ((hasDerivAt_id t).ofReal_comp.hasDerivWithinAt (s := Icc 0 T))
      simp only [sub_self, Complex.ofReal_one] at h2
      exact h2.mono_of_mem_nhdsWithin (FlowHoloAux.mem_nhdsGE_Icc ht)
    intro t ht
    have := constant_of_has_deriv_right_zero hc hd t ht
    rw [hφ0] at this
    simpa [v, sub_eq_zero] using this
  refine ⟨fun t => Fin.tail (φ t v), fun t ht => ?_, by simp [hφ0, v], fun t ht => ?_⟩
  · have h1 := (hφt t ht).1
    have h2 : HasDerivWithinAt (fun t => Fin.tail (φ t v)) (Fin.tail (augH H (φ t v)))
        (Icc 0 T) t := hasDerivWithinAt_pi.2 fun j => (hasDerivWithinAt_pi.1 h1) j.succ
    simpa [augH, htime t ht] using h2
  · exact ((hφt t ht).2).2

/-- Uniform smallness near `[0, T] × {0}` of a continuous function vanishing there. -/
theorem small_near {X : Type*} [NormedAddCommGroup X] {f : ℂ × C2 → X} {O : Set (ℂ × C2)}
    (hO : IsOpen O) (hf : ContinuousOn f O) {T : ℝ}
    (hK : ∀ t ∈ Icc 0 T, ((t : ℂ), (0 : C2)) ∈ O ∧ f ((t : ℂ), 0) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ w : C2, ‖w‖ < δ → ((t : ℂ), w) ∈ O ∧ ‖f ((t : ℂ), w)‖ < ε := by
  set V := O ∩ f ⁻¹' ball 0 ε
  have hV : IsOpen V := hf.isOpen_inter_preimage hO isOpen_ball
  set K := (fun t : ℝ => ((t : ℂ), (0 : C2))) '' Icc 0 T
  have hKc : IsCompact K := (isCompact_Icc).image
    (Complex.continuous_ofReal.prodMk continuous_const)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨(hK t ht).1, by simp [(hK t ht).2, hε]⟩
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_thickening_subset_open hV hKV
  refine ⟨δ, hδ, fun t ht w hw => ?_⟩
  have hmem : ((t : ℂ), w) ∈ thickening δ K := by
    rw [mem_thickening_iff]
    refine ⟨((t : ℂ), 0), ⟨t, ht, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, dist_zero_right]
    simpa using hw
  have := hδV hmem
  exact ⟨this.1, by simpa using this.2⟩

end ABC.S4.R123Aux
