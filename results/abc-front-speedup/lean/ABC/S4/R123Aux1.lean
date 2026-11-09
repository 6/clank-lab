import Mathlib
import ABC.S4.HoloDeriv

/-! Several complex variables: a function holomorphic on an open subset of a finite-dimensional
space is analytic there. Pinned Mathlib has this only on `ℂ`. Proof: Cauchy estimates for
iterated directional derivatives bound the Taylor series, and the one-variable Taylor expansion
along each complex line sums it. -/

open Set Metric Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace ABC.S4.R123Aux

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Cauchy estimate for a directional derivative. -/
theorem norm_fderiv_apply_le {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {y : E} {δ M : ℝ} (hδ : 0 < δ) (hsub : closedBall y δ ⊆ U)
    (hM : ∀ z ∈ closedBall y δ, ‖f z‖ ≤ M) (v : E) :
    ‖fderiv ℂ f y v‖ ≤ M / δ * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : 0 ≤ M := (norm_nonneg _).trans (hM y (mem_closedBall_self hδ.le))
    simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hρ : 0 < δ / ‖v‖ := div_pos hδ hvpos
  have hmem : ∀ z : ℂ, ‖z‖ ≤ δ / ‖v‖ → y + z • v ∈ closedBall y δ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖z‖ * ‖v‖ ≤ δ / ‖v‖ * ‖v‖ := by gcongr
      _ = δ := div_mul_cancel₀ _ hvpos.ne'
  have hdiff : ∀ z : ℂ, ‖z‖ ≤ δ / ‖v‖ → DifferentiableAt ℂ (fun z : ℂ => f (y + z • v)) z := by
    intro z hz
    have hfz : DifferentiableAt ℂ f (y + z • v) :=
      hf.differentiableAt (hU.mem_nhds (hsub (hmem z hz)))
    exact hfz.comp z ((differentiableAt_id.smul_const v).const_add y)
  have hd : DiffContOnCl ℂ (fun z : ℂ => f (y + z • v)) (ball 0 (δ / ‖v‖)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hρ.ne']
    intro z hz
    exact (hdiff z (by simpa using hz)).differentiableWithinAt
  have hC : ∀ z ∈ sphere (0 : ℂ) (δ / ‖v‖), ‖f (y + z • v)‖ ≤ M := fun z hz =>
    hM _ (hmem z (by rw [mem_sphere_zero_iff_norm] at hz; rw [hz]))
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  have hy : y ∈ U := hsub (mem_closedBall_self hδ.le)
  rw [(HoloDeriv.hasDerivAt_line (hf.differentiableAt (hU.mem_nhds hy)) v).deriv] at key
  calc _ ≤ M / (δ / ‖v‖) := key
    _ = M / δ * ‖v‖ := by field_simp

/-- Cauchy estimate for iterated derivatives, by induction on directional derivatives. -/
theorem norm_iteratedFDeriv_apply_le (n : ℕ) : ∀ {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [FiniteDimensional ℂ F] {f : E → F} {U : Set E}, IsOpen U →
    DifferentiableOn ℂ f U → ∀ {x : E} {R M : ℝ}, 0 < R → closedBall x R ⊆ U →
    (∀ z ∈ closedBall x R, ‖f z‖ ≤ M) →
    ∀ m : Fin n → E, ‖iteratedFDeriv ℂ n f x m‖ ≤ M * (n + 1) ^ n / R ^ n * ∏ i, ‖m i‖ := by
  induction n with
  | zero =>
    intro F _ _ _ f U hU hf x R M hR hsub hM m
    simpa using hM x (mem_closedBall_self hR.le)
  | succ n ih =>
    intro F _ _ _ f U hU hf x R M hR hsub hM m
    have hx : x ∈ U := hsub (mem_closedBall_self hR.le)
    obtain ⟨v, hv⟩ : ∃ v, v = m (Fin.last n) := ⟨_, rfl⟩
    have hg : DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U := fun y hy =>
      (HoloDeriv.differentiableAt_fderiv_apply hU hf hy v).differentiableWithinAt
    have hcomp : iteratedFDeriv ℂ (n + 1) f x m =
        iteratedFDeriv ℂ n (fun y => fderiv ℂ f y v) x (Fin.init m) := by
      rw [iteratedFDeriv_succ_apply_right, ← hv]
      have hc : ContDiffAt ℂ n (fderiv ℂ f) x :=
        (HoloDeriv.contDiffAt hU (HoloDeriv.differentiableOn_fderiv hU hf) hx).of_le
          (by exact_mod_cast le_top)
      have h1 := (ContinuousLinearMap.apply ℂ F v).iteratedFDeriv_comp_left hc (i := n) le_rfl
      have h2 : (fun y => fderiv ℂ f y v) = (ContinuousLinearMap.apply ℂ F v) ∘ fderiv ℂ f := rfl
      rw [h2, h1]
      rfl
    set R' : ℝ := R * (n + 1) / (n + 2)
    set δ : ℝ := R / (n + 2)
    have hδ : 0 < δ := by positivity
    have hR' : 0 < R' := by positivity
    have hRR : R' + δ = R := by simp only [R', δ]; field_simp; ring
    have hsub' : closedBall x R' ⊆ U :=
      (closedBall_subset_closedBall (by linarith)).trans hsub
    have hgM : ∀ z ∈ closedBall x R', ‖fderiv ℂ f z v‖ ≤ M / δ * ‖v‖ := by
      intro z hz
      rw [mem_closedBall] at hz
      have hzz : closedBall z δ ⊆ closedBall x R :=
        closedBall_subset_closedBall' (by linarith)
      exact norm_fderiv_apply_le hU hf hδ (hzz.trans hsub) (fun w hw => hM w (hzz hw)) v
    have key := ih hU hg hR' hsub' hgM (Fin.init m)
    rw [hcomp]
    refine key.trans (le_of_eq ?_)
    have hR'n : R' ^ n = R ^ n * ((n : ℝ) + 1) ^ n / ((n : ℝ) + 2) ^ n := by
      simp only [R']; rw [div_pow, mul_pow]
    rw [Fin.prod_univ_castSucc, hR'n, ← hv]
    simp only [Fin.init, δ]
    push_cast
    field_simp
    ring

theorem norm_iteratedFDeriv_le {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} {R M : ℝ} (hR : 0 < R) (hsub : closedBall x R ⊆ U)
    (hM : ∀ z ∈ closedBall x R, ‖f z‖ ≤ M) (hM0 : 0 ≤ M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ M * (n + 1) ^ n / R ^ n :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    (norm_iteratedFDeriv_apply_le n hU hf hR hsub hM)

/-- Taylor coefficients along a complex line. -/
theorem iteratedDeriv_line {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x y : E} {ρ : ℝ} (hρ : ∀ z : ℂ, ‖z‖ < ρ → x + z • y ∈ U) (n : ℕ) :
    ∀ z : ℂ, ‖z‖ < ρ → iteratedDeriv n (fun z : ℂ => f (x + z • y)) z =
      iteratedFDeriv ℂ n f (x + z • y) (fun _ => y) := by
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun z : ℂ => f (x + z • y)) =ᶠ[𝓝 z]
        fun z => iteratedFDeriv ℂ n f (x + z • y) (fun _ => y) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
      exact ih w hw
    rw [heq.deriv_eq]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) (x + z • y) :=
      (HoloDeriv.contDiffAt hU hf (hρ z hz)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n)
    have hline : HasDerivAt (fun w : ℂ => x + w • y) y z := by
      simpa using ((hasDerivAt_id z).smul_const y).const_add x
    have h1 := hd.hasFDerivAt.comp_hasDerivAt z hline
    have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F
      (fun _ => y)).hasFDerivAt.comp_hasDerivAt z h1
    rw [show (fun z : ℂ => iteratedFDeriv ℂ n f (x + z • y) (fun _ => y)) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y)) ∘
        (iteratedFDeriv ℂ n f ∘ fun w : ℂ => x + w • y) from rfl, h2.deriv,
      iteratedFDeriv_succ_apply_left]
    rfl

/-- **Holomorphic ⇒ analytic** in several variables. -/
theorem analyticAt {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  have := FiniteDimensional.complete ℂ F
  obtain ⟨R0, hR0, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨R, hRdef⟩ : ∃ R, R = R0 / 2 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hsub : closedBall x R ⊆ U := (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hball
  obtain ⟨M0, hM0⟩ : ∃ M, ∀ z ∈ closedBall x R, ‖f z‖ ≤ M :=
    (isCompact_closedBall x R).exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  set M := max M0 0
  have hM : ∀ z ∈ closedBall x R, ‖f z‖ ≤ M := fun z hz => (hM0 z hz).trans (le_max_left _ _)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 < Real.exp 1 := by simp
  set p : FormalMultilinearSeries ℂ E F := fun n => ((n ! : ℂ)⁻¹) • iteratedFDeriv ℂ n f x
  set r : NNReal := ⟨R / Real.exp 1, by positivity⟩
  have hpn : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ M * Real.exp 1 := by
    intro n
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have h1 : ‖p n‖ ≤ (n ! : ℝ)⁻¹ * (M * (n + 1) ^ n / R ^ n) := by
      simp only [p]
      refine (norm_smul_le ((n ! : ℂ)⁻¹) (iteratedFDeriv ℂ n f x)).trans ?_
      rw [norm_inv, Complex.norm_natCast]
      gcongr
      exact norm_iteratedFDeriv_le hU hf hR hsub hM (le_max_right _ _) n
    have h2 : ((n : ℝ) + 1) ^ n / n ! ≤ Real.exp 1 ^ n * Real.exp 1 := by
      have := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) (by positivity) (n + 1)
      rw [← pow_succ, Real.exp_one_pow]
      convert this using 1
      · rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
      · push_cast; ring_nf
    have hr : (r : ℝ) = R / Real.exp 1 := rfl
    calc ‖p n‖ * (r : ℝ) ^ n ≤ (n ! : ℝ)⁻¹ * (M * (n + 1) ^ n / R ^ n) * (R / Real.exp 1) ^ n := by
          rw [hr]; gcongr
      _ = M * (((n : ℝ) + 1) ^ n / n !) / Real.exp 1 ^ n := by
          rw [div_pow]; field_simp
      _ ≤ M * (Real.exp 1 ^ n * Real.exp 1) / Real.exp 1 ^ n := by
          gcongr
      _ = M * Real.exp 1 := by field_simp
  refine ⟨p, r, p.le_radius_of_bound _ hpn, ENNReal.coe_pos.2 (NNReal.coe_pos.1 (by show (0 : ℝ) < R / Real.exp 1; positivity)), ?_⟩
  intro y hy
  have hy' : ‖y‖ < R / Real.exp 1 := by
    have h := hy
    simp only [Metric.mem_eball, edist_zero_right] at h
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm] at h
    exact h
  have hline : ∀ z : ℂ, ‖z‖ < Real.exp 1 → x + z • y ∈ U := by
    intro z hz
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖z‖ * ‖y‖ ≤ Real.exp 1 * (R / Real.exp 1) := by gcongr
      _ = R := by field_simp
      _ < R0 := by rw [hRdef]; linarith
  have hgd : DifferentiableOn ℂ (fun z : ℂ => f (x + z • y)) (ball 0 (Real.exp 1)) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    exact ((hf.differentiableAt (hU.mem_nhds (hline z hz))).comp z
      ((differentiableAt_id.smul_const y).const_add x)).differentiableWithinAt
  have hs := Complex.hasSum_taylorSeries_on_ball hgd (z := 1) (by simp [he1])
  simp only [one_smul, sub_zero, one_pow] at hs
  convert hs using 2 with n
  rw [iteratedDeriv_line hU hf hline n 0 (by simpa using he), zero_smul, add_zero]
  rfl

theorem analyticOnNhd {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U := fun _ hx => analyticAt hU hf hx

end ABC.S4.R123Aux
