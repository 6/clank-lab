import ABC.S4.FlowComplex
import ABC.S4.R1TranslateAux1
import ABC.S4.R1TranslateAux2

/-! R1 helpers: the certified orbit in complex time `z`, extended `2π`-periodically to a strip,
via `flow_complex_time` for the autonomous field `(zField, 1)` on `ℂ³`. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.R1TranslateAux

/-- Uniqueness on an open interval, both directions from `t₀`. -/
theorem ode_unique_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) {f g : ℝ → E}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (F (f t)) t ∧ f t ∈ U)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (F (g t)) t ∧ g t ∈ U)
    (h : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  intro t ht
  rcases le_total t₀ t with h1 | h1
  · have hs : Icc t₀ t ⊆ Ioo a b := fun x hx => ⟨by linarith [ht₀.1, hx.1], by linarith [ht.2, hx.2]⟩
    exact ode_unique_C1 hU hF (fun x hx => ⟨(hf x (hs hx)).1.hasDerivWithinAt, (hf x (hs hx)).2⟩)
      (fun x hx => ⟨(hg x (hs hx)).1.hasDerivWithinAt, (hg x (hs hx)).2⟩) h ⟨h1, le_rfl⟩
  · have hs : Icc (-t₀) (-t) ⊆ Ioo (-b) (-a) :=
      fun x hx => ⟨by linarith [ht₀.2, hx.1], by linarith [ht.1, hx.2]⟩
    have hr : ∀ φ : ℝ → E, (∀ t ∈ Ioo a b, HasDerivAt φ (F (φ t)) t ∧ φ t ∈ U) →
        ∀ x ∈ Icc (-t₀) (-t), HasDerivWithinAt (fun s => φ (-s)) ((-F) (φ (-x)))
          (Icc (-t₀) (-t)) x ∧ φ (-x) ∈ U := by
      intro φ hφ x hx
      have hx' : -x ∈ Ioo a b := by have := hs hx; constructor <;> linarith [this.1, this.2]
      refine ⟨?_, (hφ _ hx').2⟩
      have := (hφ _ hx').1.scomp x (hasDerivAt_neg x)
      simpa [Function.comp_def] using this.hasDerivWithinAt
    have := ode_unique_C1 hU hF.neg (hr f hf) (hr g hg) (by simpa using h)
      ⟨neg_le_neg h1, le_rfl⟩
    simpa using this

/-- The restriction of a complex-differentiable curve to the real line. -/
lemma hasDerivAt_comp_ofReal' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {e : ℂ → E} {e' : E} {z : ℝ} (hf : HasDerivAt e e' z) :
    HasDerivAt (fun y : ℝ => e y) e' z := by
  have := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt z
    (Complex.ofRealCLM.hasDerivAt (x := z))
  simpa [Function.comp_def] using this

/-- The open rectangle `a < re t < b`, `|im t| < c`. -/
def rect (a b c : ℝ) : Set ℂ := {t | t.re ∈ Ioo a b ∧ |t.im| < c}

lemma isOpen_rect (a b c : ℝ) : IsOpen (rect a b c) := by
  have h1 : IsOpen {t : ℂ | t.re ∈ Ioo a b} := isOpen_Ioo.preimage Complex.continuous_re
  have h2 : IsOpen {t : ℂ | |t.im| < c} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

lemma convex_rect (a b c : ℝ) : Convex ℝ (rect a b c) := by
  have : rect a b c = Complex.reLm ⁻¹' Ioo a b ∩ Complex.imLm ⁻¹' Ioo (-c) c := by
    ext t; simp [rect, abs_lt]
  rw [this]
  exact ((convex_Ioo a b).linear_preimage _).inter ((convex_Ioo _ _).linear_preimage _)

/-- The autonomous extension `(zField, 1)` of the `z`-flow on `ℂ³`. -/
def F3 (ζ : Cn 3) : Cn 3 :=
  ![(Complex.sin (ζ 2) + Complex.cos (ζ 1)) / (Complex.sin (ζ 1) + Complex.cos (ζ 0)),
    (Complex.sin (ζ 0) + Complex.cos (ζ 2)) / (Complex.sin (ζ 1) + Complex.cos (ζ 0)), 1]

def U3 : Set (Cn 3) := {ζ | Complex.sin (ζ 1) + Complex.cos (ζ 0) ≠ 0}

lemma isOpen_U3 : IsOpen U3 :=
  isOpen_ne_fun (by fun_prop) continuous_const

lemma contDiffOn_F3 {n : WithTop ℕ∞} : ContDiffOn ℂ n F3 U3 := by
  have hs : ∀ i : Fin 3, ContDiff ℂ n (fun ζ : Cn 3 => Complex.sin (ζ i)) := fun i =>
    Complex.contDiff_sin.comp (contDiff_apply ℂ ℂ i)
  have hc : ∀ i : Fin 3, ContDiff ℂ n (fun ζ : Cn 3 => Complex.cos (ζ i)) := fun i =>
    Complex.contDiff_cos.comp (contDiff_apply ℂ ℂ i)
  have hden : ContDiffOn ℂ n (fun ζ : Cn 3 => Complex.sin (ζ 1) + Complex.cos (ζ 0)) U3 :=
    ((hs 1).add (hc 0)).contDiffOn
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · exact ((hs 2).add (hc 1)).contDiffOn.div hden fun x hx => hx
  · exact ((hs 0).add (hc 2)).contDiffOn.div hden fun x hx => hx
  · exact contDiffOn_const

lemma vec2_eta (q : C2) : (![q 0, q 1] : C2) = q := by
  ext i; fin_cases i <;> rfl

/-- `F3` in terms of `zField`. -/
lemma F3_eq (ζ : Cn 3) :
    F3 ζ = ![zField ![ζ 0, ζ 1] (ζ 2) 0, zField ![ζ 0, ζ 1] (ζ 2) 1, 1] := by
  simp [F3, zField]

lemma zField_sub_period (q : C2) (t : ℂ) (m : ℤ) :
    zField q (t - 2 * π * m) = zField q t := by
  have h : t - 2 * π * m = t - m * (2 * π) := by ring
  simp only [zField, h, Complex.sin_sub_int_mul_two_pi, Complex.cos_sub_int_mul_two_pi]

section orbit

variable {p : E 2} (hp : CertFacts p)
include hp

/-- The real orbit from `a`, lifted to `ℂ³` with `z` as third coordinate. -/
lemma hasDerivAt_lift3 {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Ioo (-7 : ℝ) 7) :
    HasDerivAt (fun t : ℝ => (![ofR (crossP a t) 0, ofR (crossP a t) 1, (t : ℂ)] : Cn 3))
      (F3 ![ofR (crossP a c) 0, ofR (crossP a c) 1, (c : ℂ)]) c := by
  have h := hasDerivAt_pi.1 (hasDerivAt_crossP hp ha hc)
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [F3_eq, vec2_eta] using h 0
  · simpa [F3_eq, vec2_eta] using h 1
  · simpa [F3] using (hasDerivAt_id c).ofReal_comp

lemma lift3_mem {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    (![ofR (crossP a c) 0, ofR (crossP a c) 1, (c : ℂ)] : Cn 3) ∈ U3 := by
  have h := crossP_Vz hp ha hc
  show Complex.sin _ + Complex.cos _ ≠ 0
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, ofR]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_add]
  exact_mod_cast (by linarith : (0 : ℝ) < _).ne'

/-- The certified orbit, holomorphic and `2π`-periodic in complex `z` on a strip. -/
theorem complex_orbit : ∃ s > 0, ∃ M : ℝ, ∃ Q : ℂ → C2,
    (∀ t, Q (t + 2 * π) = Q t) ∧
    (∀ t ∈ strip s, HasDerivAt Q (zField (Q t) t) t) ∧
    (∀ t ∈ strip s, ‖Q t‖ ≤ M ∧ 1 ≤ ‖Complex.sin (Q t 1) + Complex.cos (Q t 0)‖) ∧
    (∀ t : ℝ, t ∈ Icc 0 (2 * π) → Q t = ofR (crossP p t)) ∧
    (∀ t : ℝ, ∃ x : E 2, Q t = ofR x) := by
  have hp0 : p ∈ closedBall p r₀ := mem_closedBall_self r₀_pos.le
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  set γ3 : ℝ → Cn 3 := fun t => ![ofR (crossP p t) 0, ofR (crossP p t) 1, (t : ℂ)] with hγ3
  have hγd : ∀ t ∈ Ioo (-7 : ℝ) 7, HasDerivAt γ3 (F3 (γ3 t)) t ∧ γ3 t ∈ U3 := fun t ht =>
    ⟨hasDerivAt_lift3 hp hp0 ht, lift3_mem hp hp0 (Ioo_subset_Icc_self ht)⟩
  obtain ⟨s₀, hs₀, r, hr, φ, -, hφ⟩ := flow_complex_time isOpen_U3
    ((contDiffOn_F3 (n := 1)).differentiableOn one_ne_zero) (γ := γ3) (T := 2 * π)
    (by positivity)
    (fun t ht => ⟨(hγd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.hasDerivWithinAt,
      (hγd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2⟩)
  obtain ⟨hZ0, hZ⟩ := hφ (γ3 0) (mem_ball_self hr)
  set Z : ℂ → Cn 3 := fun t => φ t (γ3 0) with hZdef
  set R0 := rect (-s₀) (2 * π + s₀) s₀ with hR0
  have hZR : ∀ t ∈ R0, HasDerivAt Z (F3 (Z t)) t ∧ Z t ∈ U3 := fun t ht => hZ t ht.1 ht.2
  have h0R : (0 : ℂ) ∈ R0 := ⟨⟨by simp; linarith, by simp; linarith⟩, by simpa using hs₀⟩
  -- the third coordinate is `t`
  have hZ2 : ∀ t ∈ R0, Z t 2 = t := by
    have hg : ∀ t ∈ R0, HasDerivAt (fun t => Z t 2 - t) 0 t := by
      intro t ht
      have h2 := (hasDerivAt_pi.1 (hZR t ht).1) 2
      have : HasDerivAt (fun t => Z t 2 - t) (F3 (Z t) 2 - 1) t := h2.sub (hasDerivAt_id' t)
      convert this using 1
      simp [F3]
    intro t ht
    have := (convex_rect _ _ _).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (f := fun t => Z t 2 - t) (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [fderivWithin_of_isOpen (isOpen_rect _ _ _) hx, (hg x hx).hasFDerivAt.fderiv]
        simp) ht h0R
    have hz0 : Z 0 2 = 0 := by
      show φ 0 (γ3 0) 2 = 0
      rw [hZ0]; simp [γ3]
    simp only [hz0, sub_zero] at this
    linear_combination this
  -- on the real axis `Z` is the real orbit
  set s₁ := min s₀ (7 / 10) with hs₁def
  have hs₁ : 0 < s₁ := lt_min hs₀ (by norm_num)
  have hs₁0 : s₁ ≤ s₀ := min_le_left _ _
  have hs₁7 : s₁ ≤ 7 / 10 := min_le_right _ _
  have hZreal : ∀ t ∈ Ioo (-s₁) (2 * π + s₁), Z t = γ3 t := by
    have hsub : ∀ t ∈ Ioo (-s₁) (2 * π + s₁), (t : ℂ) ∈ R0 := fun t ht =>
      ⟨⟨by simp; linarith [ht.1], by simp; linarith [ht.2]⟩, by simpa using hs₀⟩
    intro t ht
    refine ode_unique_Ioo (f := fun t : ℝ => Z t) isOpen_U3
      ((contDiffOn_F3 (n := 1)).restrict_scalars ℝ) (t₀ := 0)
      ⟨by linarith, by linarith [Real.pi_pos]⟩ ?_ ?_ ?_ ht
    · intro t ht
      exact ⟨hasDerivAt_comp_ofReal' (hZR t (hsub t ht)).1, (hZR t (hsub t ht)).2⟩
    · intro t ht
      exact hγd t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · show Z ((0 : ℝ) : ℂ) = γ3 0
      rw [Complex.ofReal_zero]; exact hZ0
  set Q : ℂ → C2 := fun t => ![Z t 0, Z t 1] with hQdef
  have hQd : ∀ t ∈ R0, HasDerivAt Q (zField (Q t) t) t := by
    intro t ht
    have h := hasDerivAt_pi.1 (hZR t ht).1
    have e := hZ2 t ht
    rw [hasDerivAt_pi]; intro i
    fin_cases i
    · simpa [Q, F3_eq, e] using h 0
    · simpa [Q, F3_eq, e] using h 1
  have hQreal : ∀ t ∈ Ioo (-s₁) (2 * π + s₁), Q t = ofR (crossP p t) := by
    intro t ht
    have := hZreal t ht
    ext i; fin_cases i <;> simp [Q, this, γ3]
  -- periodicity near `re t = 0`, by the identity theorem
  set D := rect (-s₁) s₁ s₁ with hD
  have hDR : ∀ t ∈ D, t ∈ R0 ∧ t + 2 * π ∈ R0 := by
    intro t ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩,
      ⟨⟨by simp; linarith, by simp; linarith⟩, by simp; linarith⟩⟩
  have hQper0 : ∀ t ∈ D, Q (t + 2 * π) = Q t := by
    have hA1 : AnalyticOnNhd ℂ (fun t => Q (t + 2 * π)) D :=
      DifferentiableOn.analyticOnNhd (fun t ht =>
        ((hQd _ (hDR t ht).2).differentiableAt.comp t
          (differentiableAt_id.add_const _)).differentiableWithinAt) (isOpen_rect _ _ _)
    have hA2 : AnalyticOnNhd ℂ Q D :=
      DifferentiableOn.analyticOnNhd (fun t ht =>
        (hQd _ (hDR t ht).1).differentiableAt.differentiableWithinAt) (isOpen_rect _ _ _)
    have h0D : (0 : ℂ) ∈ D := ⟨⟨by simp; linarith, by simp; linarith⟩, by simpa using hs₁⟩
    have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
        simpa using this
      · simpa using hx
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), Q ((t : ℂ) + 2 * π) = Q (t : ℂ) := by
      have : Ioo (-s₁) s₁ ∈ 𝓝[≠] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hs₁)
      filter_upwards [this] with t ht
      rw [show (t : ℂ) + 2 * π = ((t + 2 * π : ℝ) : ℂ) by push_cast; ring,
        hQreal _ ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩,
        hQreal t ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩,
        crossP_p_periodic hp (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    exact hA1.eqOn_of_preconnected_of_frequently_eq hA2 (convex_rect _ _ _).isPreconnected h0D
      (hT.frequently hev.frequently)
  -- the periodic extension
  set k : ℂ → ℤ := fun t => ⌊t.re / (2 * π)⌋ with hkdef
  set Qp : ℂ → C2 := fun t => Q (t - 2 * π * (k t)) with hQpdef
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hk : ∀ t : ℂ, (t - 2 * π * (k t)).re ∈ Ico 0 (2 * π) := by
    intro t
    have h1 := Int.floor_le (t.re / (2 * π))
    have h2 := Int.lt_floor_add_one (t.re / (2 * π))
    have e : (t - 2 * π * (k t)).re = t.re - 2 * π * (k t) := by simp
    rw [e]
    have h1' : 2 * π * (k t) ≤ t.re := by
      have := mul_le_mul_of_nonneg_left h1 h2pi.le
      rwa [mul_div_cancel₀ _ h2pi.ne'] at this
    have h2' : t.re < 2 * π * (k t) + 2 * π := by
      have := mul_lt_mul_of_pos_left h2 h2pi
      rw [mul_div_cancel₀ _ h2pi.ne'] at this
      linarith
    exact ⟨by linarith, by linarith⟩
  have hcons : ∀ t : ℂ, |t.im| < s₁ → ∀ m : ℤ,
      (t - 2 * π * m).re ∈ Ioo (-s₁) (2 * π + s₁) → Qp t = Q (t - 2 * π * m) := by
    intro t ht m hm
    have hk' := hk t
    set τ := t - 2 * π * (k t) with hτ
    have hre : (t - 2 * π * m).re = τ.re + 2 * π * ((k t : ℝ) - m) := by simp [τ]; ring
    rw [hre] at hm
    have hlo : ((k t - m : ℤ) : ℝ) > -2 := by
      push_cast
      by_contra hc; push Not at hc
      nlinarith [hm.1, hk'.1, hk'.2]
    have hhi : ((k t - m : ℤ) : ℝ) < 2 := by
      push_cast
      by_contra hc; push Not at hc
      nlinarith [hm.2, hk'.1, hk'.2]
    have hlo' : k t - m > -2 := by exact_mod_cast hlo
    have hhi' : k t - m < 2 := by exact_mod_cast hhi
    have hcases : m = k t ∨ m = k t - 1 ∨ m = k t + 1 := by omega
    have him : (τ).im = t.im := by simp [τ]
    rcases hcases with rfl | rfl | rfl
    · rfl
    · -- `t - 2π m = τ + 2π`
      have e : t - 2 * π * ((k t - 1 : ℤ) : ℂ) = τ + 2 * π := by simp [τ]; ring
      rw [e]
      have hm' : τ.re < s₁ := by push_cast at hm; linarith [hm.2]
      exact (hQper0 τ ⟨⟨by linarith [hk'.1], hm'⟩, by rw [him]; exact ht⟩).symm
    · have e : t - 2 * π * ((k t + 1 : ℤ) : ℂ) = τ - 2 * π := by simp [τ]; ring
      rw [e]
      have hm' : -s₁ < τ.re - 2 * π := by push_cast at hm; linarith [hm.1]
      have hmem : τ - 2 * π ∈ D := ⟨⟨by simpa using hm', by simp; linarith [hk'.2]⟩,
        by simpa [him] using ht⟩
      have := hQper0 _ hmem
      rw [sub_add_cancel] at this
      exact this
  have hQp_per : ∀ t, Qp (t + 2 * π) = Qp t := by
    intro t
    have : k (t + 2 * π) = k t + 1 := by
      simp only [k, Complex.add_re, Complex.ofReal_re]
      rw [show (t.re + (2 * π : ℂ).re) / (2 * π) = t.re / (2 * π) + 1 by
        simp; field_simp]
      exact Int.floor_add_one _
    simp only [Qp, this]
    congr 1; push_cast; ring
  -- bounds by compactness
  have hQcont : ContinuousOn Q R0 := fun t ht => (hQd t ht).continuousAt.continuousWithinAt
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc 0 (2 * π) with hKdef
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKR : K ⊆ R0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩, by simpa using hs₀⟩
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hQcont.mono hKR)
  set O : Set ℂ := R0 ∩ Q ⁻¹' {q | ‖q‖ < M₀ + 1 ∧ 1 < ‖Complex.sin (q 1) + Complex.cos (q 0)‖}
  have hO : IsOpen O := hQcont.isOpen_inter_preimage (isOpen_rect _ _ _)
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const ((Complex.continuous_sin.comp (continuous_apply 1)).add
        (Complex.continuous_cos.comp (continuous_apply 0))).norm))
  have hKO : K ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hKR ⟨x, hx, rfl⟩, ?_, ?_⟩
    · have := hM₀ _ ⟨x, hx, rfl⟩; linarith
    · rw [hQreal x ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      have hV := crossP_p_Vz hp (c := x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      simp only [ofR]
      rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_thickening_subset_open hO hKO
  refine ⟨min s₁ δ, lt_min hs₁ hδ, M₀ + 1, Qp, hQp_per, ?_, ?_, ?_, ?_⟩
  · -- derivative
    intro t ht
    have ht' : |t.im| < s₁ := lt_of_lt_of_le ht (min_le_left _ _)
    have hτ := hk t
    set m := k t
    have hτR : t - 2 * π * m ∈ R0 :=
      ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, by simpa using ht'.trans_le hs₁0⟩
    have hev : (fun u => Q (u - 2 * π * m)) =ᶠ[𝓝 t] Qp := by
      have h1 : {u : ℂ | |u.im| < s₁} ∈ 𝓝 t :=
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds ht'
      have h2 : {u : ℂ | (u - 2 * π * m).re ∈ Ioo (-s₁) (2 * π + s₁)} ∈ 𝓝 t :=
        (isOpen_Ioo.preimage (Complex.continuous_re.comp (continuous_sub_right _))).mem_nhds
          (show (t - 2 * π * m).re ∈ Ioo (-s₁) (2 * π + s₁) from
            ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
      filter_upwards [h1, h2] with u hu1 hu2
      exact (hcons u hu1 m hu2).symm
    have hd := (hQd _ hτR).scomp t ((hasDerivAt_id' t).sub_const (2 * (π : ℂ) * (m : ℂ)))
    simp only [one_smul, Function.comp_def] at hd
    rw [zField_sub_period] at hd
    exact hd.congr_of_eventuallyEq hev.symm
  · -- bounds
    intro t ht
    have ht' : |t.im| < δ := lt_of_lt_of_le ht (min_le_right _ _)
    set τ := t - 2 * π * (k t)
    have hτ := hk t
    have hmem : τ ∈ thickening δ K := by
      rw [mem_thickening_iff]
      refine ⟨(τ.re : ℂ), ⟨τ.re, ⟨hτ.1, hτ.2.le⟩, rfl⟩, ?_⟩
      rw [Complex.dist_of_re_eq (by simp), Real.dist_eq]
      simpa [τ] using ht'
    obtain ⟨-, h1, h2⟩ := hδO hmem
    exact ⟨h1.le, h2.le⟩
  · -- the real orbit on `[0, 2π]`
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      have e : ((2 * π : ℝ) : ℂ) = 0 + 2 * π := by push_cast; ring
      rw [e, hQp_per, crossP_p_pos hp]
      have hk0 : k 0 = 0 := by simp [k]
      simp only [Qp, hk0]
      simp only [Int.cast_zero, mul_zero, sub_zero]
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, hQreal 0 ⟨by linarith, by linarith⟩,
        crossP_zero hp hp0]
    · have hk0 : k t = 0 := by
        simp only [k, Complex.ofReal_re]
        rw [Int.floor_eq_zero_iff]
        exact ⟨div_nonneg ht.1 h2pi.le, (div_lt_one h2pi).2 h⟩
      simp only [Qp, hk0, Int.cast_zero, mul_zero, sub_zero]
      exact hQreal t ⟨by linarith [ht.1], by linarith⟩
  · -- real values
    intro t
    have hτ := hk t
    refine ⟨crossP p (t - 2 * π * (k t)), ?_⟩
    have e : (t : ℂ) - 2 * π * (k (t : ℂ)) = ((t - 2 * π * (k (t : ℂ)) : ℝ) : ℂ) := by push_cast; ring
    have hre : ((t : ℂ) - 2 * π * (k (t : ℂ))).re = t - 2 * π * (k (t : ℂ)) := by simp
    simp only [Qp]
    rw [e, hQreal]
    rw [hre] at hτ
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

end orbit

end ABC.S4.R1TranslateAux
