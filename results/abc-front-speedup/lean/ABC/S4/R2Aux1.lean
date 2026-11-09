import Mathlib

/-! R2 helpers, general: local-Lipschitz ODE uniqueness, an order-3 Schwarz bound, the elliptic
normal form in `SL(2,ℝ)`, and realness of derivatives of functions real on real points. -/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace ABC.S4.R2Aux

/-- Uniqueness for `ẋ = v t x` when `v` is Lipschitz near the curve `f` (no a priori bound on
`g`). -/
theorem local_unique {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : ℝ → V → V} {f g : ℝ → V} {a b : ℝ}
    (hlip : ∀ t ∈ Ico a b, ∃ δ > 0, ∃ ε > 0, ∃ K : ℝ≥0, ∀ u ∈ Icc t (t + δ),
      LipschitzOnWith K (v u) (ball (f t) ε))
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (v t (f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (v t (g t)) (Icc a b) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  have hcl : IsClosed ({t | f t = g t} ∩ Icc a b) := by
    have := (hfc.sub hgc).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : V)))
    convert this using 1
    ext t; simp [sub_eq_zero, and_comm]
  intro t ht
  refine (IsClosed.Icc_subset_of_forall_mem_nhdsWithin hcl ha ?_) ht
  rintro x ⟨hx, hxa, hxb⟩
  obtain ⟨δ, hδ, ε, hε, K, hK⟩ := hlip x ⟨hxa, hxb⟩
  have hxI : x ∈ Icc a b := ⟨hxa, hxb.le⟩
  have h1 : ∀ᶠ u in 𝓝[Icc a b] x, f u ∈ ball (f x) ε ∧ g u ∈ ball (f x) ε := by
    refine ((hfc x hxI).eventually (ball_mem_nhds _ hε)).and ?_
    have := (hgc x hxI).eventually (ball_mem_nhds _ hε)
    rwa [← show f x = g x from hx] at this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨η, hη, hη'⟩ := h1
  set c := min (x + δ) (min (x + η / 2) b) with hc
  have hxc : x < c := by
    simp only [hc, lt_min_iff]; exact ⟨by linarith, by linarith, hxb⟩
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Icc x c ⊆ Icc a b := Icc_subset_Icc hxa hcb
  have hmem : ∀ u ∈ Ico x c, f u ∈ ball (f x) ε ∧ g u ∈ ball (f x) ε := by
    intro u hu
    refine hη' ?_ (hsub (Ico_subset_Icc_self hu))
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
    have : u < x + η / 2 := lt_of_lt_of_le hu.2 ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hnhds : ∀ u ∈ Ico x c, Icc a b ∈ 𝓝[≥] u := fun u hu =>
    Icc_mem_nhdsGE_of_mem ⟨hxa.trans hu.1, lt_of_lt_of_le hu.2 hcb⟩
  have heq : EqOn f g (Icc x c) := by
    refine ODE_solution_unique_of_mem_Icc_right (s := fun _ => ball (f x) ε) (K := K)
      (fun u hu => hK u ⟨hu.1, hu.2.le.trans (min_le_left _ _)⟩) (hfc.mono hsub)
      (fun u hu => (hf u (hsub (Ico_subset_Icc_self hu))).mono_of_mem_nhdsWithin (hnhds u hu))
      (fun u hu => (hmem u hu).1) (hgc.mono hsub)
      (fun u hu => (hg u (hsub (Ico_subset_Icc_self hu))).mono_of_mem_nhdsWithin (hnhds u hu))
      (fun u hu => (hmem u hu).2) hx
  exact mem_of_superset (Icc_mem_nhdsGT hxc) fun u hu => heq hu

/-- Order-3 Schwarz lemma. -/
theorem cubic_bound {f : ℂ → ℂ} {R M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) (h1 : deriv f 0 = 0)
    (h2 : deriv (deriv f) 0 = 0) {r : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ M / r ^ 3 * ‖z‖ ^ 3 := by
  have hR : 0 < R := hr.trans hrR
  have hB : ball (0 : ℂ) R ∈ 𝓝 0 := ball_mem_nhds _ hR
  set f₁ := dslope f 0
  set f₂ := dslope f₁ 0
  set f₃ := dslope f₂ 0
  have hd₁ : DifferentiableOn ℂ f₁ (ball 0 R) := (Complex.differentiableOn_dslope hB).2 hf
  have hd₂ : DifferentiableOn ℂ f₂ (ball 0 R) := (Complex.differentiableOn_dslope hB).2 hd₁
  have hd₃ : DifferentiableOn ℂ f₃ (ball 0 R) := (Complex.differentiableOn_dslope hB).2 hd₂
  have e₁ : ∀ w, f w = w * f₁ w := by
    intro w; have := sub_smul_dslope f 0 w; simp only [sub_zero, smul_eq_mul, h0] at this
    exact this.symm
  have f₁0 : f₁ 0 = 0 := by simp [f₁, dslope_same, h1]
  have e₂ : ∀ w, f₁ w = w * f₂ w := by
    intro w; have := sub_smul_dslope f₁ 0 w; simp only [sub_zero, smul_eq_mul, f₁0] at this
    exact this.symm
  -- `f'' 0 = 2 f₁' 0`
  have hdd₁ : DifferentiableOn ℂ (deriv f₁) (ball 0 R) := hd₁.deriv isOpen_ball
  have hderiv : ∀ w ∈ ball (0 : ℂ) R, deriv f w = f₁ w + w * deriv f₁ w := by
    intro w hw
    have hw' : ball (0 : ℂ) R ∈ 𝓝 w := isOpen_ball.mem_nhds hw
    have hfe : f =ᶠ[𝓝 w] fun w => w * f₁ w := Filter.Eventually.of_forall e₁
    rw [hfe.deriv_eq]
    have : HasDerivAt (fun w => w * f₁ w) (1 * f₁ w + w * deriv f₁ w) w :=
      (hasDerivAt_id' w).mul (hd₁.differentiableAt hw').hasDerivAt
    rw [this.deriv]; ring
  have f₁'0 : deriv f₁ 0 = 0 := by
    have hfe : deriv f =ᶠ[𝓝 0] fun w => f₁ w + w * deriv f₁ w :=
      Filter.eventually_of_mem hB hderiv
    have hA : HasDerivAt (fun w => f₁ w + w * deriv f₁ w)
        (deriv f₁ 0 + (1 * deriv f₁ 0 + 0 * deriv (deriv f₁) 0)) 0 :=
      (hd₁.differentiableAt hB).hasDerivAt.add
        ((hasDerivAt_id' (0 : ℂ)).mul (hdd₁.differentiableAt hB).hasDerivAt)
    rw [hfe.deriv_eq, hA.deriv] at h2
    simp at h2
    exact h2
  have f₂0 : f₂ 0 = 0 := by simp [f₂, dslope_same, f₁'0]
  have e₃ : ∀ w, f₂ w = w * f₃ w := by
    intro w; have := sub_smul_dslope f₂ 0 w; simp only [sub_zero, smul_eq_mul, f₂0] at this
    exact this.symm
  have efull : ∀ w, f w = w ^ 3 * f₃ w := by
    intro w; rw [e₁, e₂, e₃]; ring
  -- maximum modulus for `f₃` on `ball 0 r`
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have hdc : DiffContOnCl ℂ f₃ (ball 0 r) := hd₃.diffContOnCl_ball hsub
  have hbd : ∀ w ∈ frontier (ball (0 : ℂ) r), ‖f₃ w‖ ≤ M / r ^ 3 := by
    intro w hw
    rw [frontier_ball _ hr.ne'] at hw
    have hwn : ‖w‖ = r := by simpa using hw
    have hfw := hM w (hsub (sphere_subset_closedBall hw))
    rw [efull w, norm_mul, norm_pow, hwn] at hfw
    rw [le_div_iff₀ (by positivity)]; linarith
  have hz' : z ∈ closure (ball (0 : ℂ) r) := by
    rw [closure_ball _ hr.ne']; simpa using hz
  have := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbd hz'
  rw [efull z, norm_mul, norm_pow]
  calc ‖z‖ ^ 3 * ‖f₃ z‖ ≤ ‖z‖ ^ 3 * (M / r ^ 3) := by gcongr
    _ = M / r ^ 3 * ‖z‖ ^ 3 := by ring

theorem nf_algebra (a β γ d c s μ k l : ℝ) (hμ0 : 0 < μ) (hs0 : s ≠ 0) (hμ2 : μ ^ 2 = l)
    (hsk : s * k = a - c) (hsl : s * l = -γ) (hss : s ^ 2 = 1 - c ^ 2)
    (hdet : a * d - β * γ = 1) (hc : c = (a + d) / 2) :
    (1 / μ) * μ - (-k / μ) * 0 = 1 ∧
      a * (1 / μ) + β * 0 = (1 / μ) * c - (-k / μ) * s ∧
      a * (-k / μ) + β * μ = (1 / μ) * s + (-k / μ) * c ∧
      γ * (1 / μ) + d * 0 = 0 * c - μ * s ∧
      γ * (-k / μ) + d * μ = 0 * s + μ * c := by
  have hμ : μ ≠ 0 := hμ0.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; linear_combination -hsk
  · field_simp
    rw [hμ2]
    apply mul_left_cancel₀ hs0
    linear_combination (c - a) * hsk + β * hsl - hss + hdet + 2 * a * hc
  · field_simp; linear_combination s * hμ2 + hsl
  · field_simp
    apply mul_left_cancel₀ hs0
    linear_combination (-γ) * hsk + (d - c) * hsl + (d - c) * s * hμ2 + 2 * γ * hc

/-- Elliptic normal form in `SL(2,ℝ)`: `M S = S R(θ)`, `R(θ) = [[cos, sin], [-sin, cos]]`. -/
theorem elliptic_normal_form (a β γ d : ℝ) (hdet : a * d - β * γ = 1) (htr : |a + d| < 2) :
    ∃ S₀₀ S₀₁ S₁₀ S₁₁ θ : ℝ, S₀₀ * S₁₁ - S₀₁ * S₁₀ = 1 ∧ Real.cos θ = (a + d) / 2 ∧
      a * S₀₀ + β * S₁₀ = S₀₀ * Real.cos θ - S₀₁ * Real.sin θ ∧
      a * S₀₁ + β * S₁₁ = S₀₀ * Real.sin θ + S₀₁ * Real.cos θ ∧
      γ * S₀₀ + d * S₁₀ = S₁₀ * Real.cos θ - S₁₁ * Real.sin θ ∧
      γ * S₀₁ + d * S₁₁ = S₁₀ * Real.sin θ + S₁₁ * Real.cos θ := by
  set c := (a + d) / 2 with hc
  have hc1 : |c| < 1 := by rw [hc, abs_div]; norm_num; linarith
  have hc1' := abs_lt.1 hc1
  have hγ : γ ≠ 0 := by
    intro h; rw [h, mul_zero, sub_zero] at hdet
    have : (a + d) ^ 2 < 4 := by nlinarith [abs_lt.1 htr]
    nlinarith [sq_nonneg (a - d)]
  have hac : 0 < Real.sin (Real.arccos c) := by
    rw [Real.sin_arccos]; apply Real.sqrt_pos.2; nlinarith
  obtain ⟨θ, hθc, hθs⟩ : ∃ θ, Real.cos θ = c ∧ γ / Real.sin θ < 0 := by
    have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos (by linarith) (by linarith)
    rcases lt_or_gt_of_ne hγ with h | h
    · exact ⟨Real.arccos c, hcos, div_neg_of_neg_of_pos h hac⟩
    · refine ⟨-Real.arccos c, by rw [Real.cos_neg, hcos], ?_⟩
      rw [Real.sin_neg]; exact div_neg_of_pos_of_neg h (by linarith)
  set s := Real.sin θ with hs
  have hs0 : s ≠ 0 := by intro h; rw [h, div_zero] at hθs; exact lt_irrefl _ hθs
  have hss : s ^ 2 = 1 - c ^ 2 := by rw [hs, ← hθc]; nlinarith [Real.sin_sq_add_cos_sq θ]
  set l := -γ / s with hl
  have hl0 : 0 < l := by rw [hl, neg_div]; linarith
  set μ := Real.sqrt l with hμ
  have hμ0 : 0 < μ := Real.sqrt_pos.2 hl0
  have hμ2 : μ ^ 2 = l := Real.sq_sqrt hl0.le
  set k := (a - c) / s with hk
  have hsk : s * k = a - c := by rw [hk]; field_simp
  have hsl : s * l = -γ := by rw [hl]; field_simp
  obtain ⟨e1, e2, e3, e4, e5⟩ := nf_algebra a β γ d c s μ k l hμ0 hs0 hμ2 hsk hsl hss hdet hc
  exact ⟨1 / μ, -k / μ, 0, μ, θ, e1, hθc, by rw [hθc]; exact e2, by rw [hθc]; exact e3,
    by rw [hθc]; exact e4, by rw [hθc]; exact e5⟩

/-- Directional derivatives of a function real on real points are real. -/
theorem im_fderiv_eq_zero {n : ℕ} {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hx : ∀ i, (x i).im = 0) (hg : DifferentiableAt ℂ g x)
    (hreal : ∀ᶠ y in 𝓝 x, (∀ i, (y i).im = 0) → (g y).im = 0) (k : Fin n) :
    (fderiv ℂ g x (Pi.single k 1)).im = 0 := by
  set e : Fin n → ℂ := Pi.single k 1
  have h1 : HasDerivAt (fun z : ℂ => x + z • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add x
  have hg' : HasFDerivAt g (fderiv ℂ g x) (x + (0 : ℂ) • e) := by simpa using hg.hasFDerivAt
  have h2 := (hg'.comp_hasDerivAt (0 : ℂ) h1).comp_ofReal (z := 0)
  have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using h2)
  have hcont : Tendsto (fun s : ℝ => x + (s : ℂ) • e) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun s : ℝ => x + (s : ℂ) • e) := by fun_prop
    simpa using this.tendsto 0
  have hev : (fun s : ℝ => Complex.imCLM (g (x + (s : ℂ) • e))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hcont.eventually hreal] with s hs
    refine hs fun i => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im, hx i, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add, e]
    by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_apply, h]
  have h4 := h3.congr_of_eventuallyEq hev.symm
  have := h4.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simpa [e] using this

end ABC.S4.R2Aux
