import Mathlib

/-! Holomorphic maps on finite-dimensional spaces are analytic (Cauchy along complex lines). -/

open Set Metric Filter Topology Complex
open scoped Real

noncomputable section

namespace ABC.S4.PeriodMapAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma hasDerivAt_line {f : E → F} {x v : E} {z : ℂ} (hf : DifferentiableAt ℂ f (x + z • v)) :
    HasDerivAt (fun w : ℂ => f (x + w • v)) (fderiv ℂ f (x + z • v) v) z := by
  have h1 : HasDerivAt (fun w : ℂ => x + w • v) v z := by
    simpa using ((hasDerivAt_id z).smul_const v).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt z h1

lemma line_mem {x v : E} {R : ℝ} {w : ℂ} (hw : ‖w‖ * ‖v‖ ≤ R) : x + w • v ∈ closedBall x R := by
  rwa [mem_closedBall, dist_self_add_left, norm_smul]

-- Cauchy's estimate along complex lines
lemma norm_fderiv_le {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} {R M : ℝ} (hR : 0 < R) (hb : closedBall x R ⊆ U)
    (hM : ∀ y ∈ closedBall x R, ‖f y‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M / R := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hR.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hR.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmem : ∀ w : ℂ, ‖w‖ ≤ R / ‖v‖ → x + w • v ∈ closedBall x R := fun w hw =>
    line_mem (by rwa [le_div_iff₀ hv'] at hw)
  have hd : ∀ w : ℂ, ‖w‖ ≤ R / ‖v‖ →
      HasDerivAt (fun w : ℂ => f (x + w • v)) (fderiv ℂ f (x + w • v) v) w := fun w hw =>
    hasDerivAt_line ((hf _ (hb (hmem w hw))).differentiableAt (hU.mem_nhds (hb (hmem w hw))))
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f (x + w • v)) (ball 0 (R / ‖v‖)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (div_pos hR hv').ne']
    intro w hw
    exact (hd w (by simpa using hw)).differentiableAt.differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hR hv') hdc
    (fun w hw => hM _ (hmem w (mem_sphere_zero_iff_norm.1 hw).le))
  rw [(hd 0 (by simp; positivity)).deriv] at h
  simp only [zero_smul, add_zero] at h
  calc ‖fderiv ℂ f x v‖ ≤ M / (R / ‖v‖) := h
    _ = M / R * ‖v‖ := by field_simp

-- Cauchy's formula along complex lines
lemma fderiv_apply_eq_circleIntegral [CompleteSpace F] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x v : E} (hb : closedBall x ‖v‖ ⊆ U) :
    fderiv ℂ f x v = (2 * π * I)⁻¹ • ∮ z in C(0, 1), (1 / z ^ 2) • f (x + z • v) := by
  have hmem : ∀ w ∈ closedBall (0 : ℂ) 1, x + w • v ∈ U := fun w hw =>
    hb (line_mem (by simpa using mul_le_of_le_one_left (norm_nonneg v) (mem_closedBall_zero_iff.1 hw)))
  have hd : ∀ w ∈ closedBall (0 : ℂ) 1,
      HasDerivAt (fun w : ℂ => f (x + w • v)) (fderiv ℂ f (x + w • v) v) w := fun w hw =>
    hasDerivAt_line ((hf _ (hmem w hw)).differentiableAt (hU.mem_nhds (hmem w hw)))
  have h := DifferentiableOn.deriv_eq_smul_circleIntegral (c := (0 : ℂ)) one_pos
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
  rw [(hd 0 (mem_closedBall_self zero_le_one)).deriv] at h
  simp only [sub_zero, zero_smul, add_zero] at h
  rw [h, smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_smul]

lemma exists_bound {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E}
    (hx : x ∈ U) : ∃ r > 0, ∃ M, closedBall x r ⊆ U ∧ ∀ y ∈ closedBall x r, ‖f y‖ ≤ M := by
  obtain ⟨r₁, hr₁, hb⟩ := Metric.isOpen_iff.1 hU x hx
  have hc : ContinuousAt f x := (hf x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
  obtain ⟨r₂, hr₂, hr⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  refine ⟨min r₁ r₂ / 2, by positivity, ‖f x‖ + 1, fun y hy => hb ?_, fun y hy => ?_⟩
  · rw [mem_closedBall] at hy; rw [mem_ball]
    linarith [min_le_left r₁ r₂, lt_min hr₁ hr₂]
  · rw [mem_closedBall] at hy
    have := hr (show dist y x < r₂ by linarith [min_le_right r₁ r₂, lt_min hr₁ hr₂])
    have h2 := norm_le_norm_add_norm_sub' (f y) (f x)
    rw [dist_eq_norm] at this
    linarith

-- `‖Df‖ ≤ 2M/r` on `closedBall x (r/2)`
lemma norm_fderiv_le_half {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} {r M : ℝ} (hr : 0 < r) (hb : closedBall x r ⊆ U)
    (hM : ∀ y ∈ closedBall x r, ‖f y‖ ≤ M) :
    ∀ y ∈ closedBall x (r / 2), ‖fderiv ℂ f y‖ ≤ M / (r / 2) := by
  intro y hy
  have hs : closedBall y (r / 2) ⊆ closedBall x r := by
    intro z hz; rw [mem_closedBall] at *; linarith [dist_triangle z y x]
  exact norm_fderiv_le hU hf (by positivity) (hs.trans hb) fun z hz => hM z (hs hz)

lemma continuousOn_fderiv {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨r, hr, M, hb, hM⟩ := exists_bound hU hf hx
  have hD := norm_fderiv_le_half hU hf hr hb hM
  have hda : ∀ y ∈ closedBall x r, DifferentiableAt ℂ f y := fun y hy =>
    (hf y (hb hy)).differentiableAt (hU.mem_nhds (hb hy))
  refine continuousAt_of_locally_lipschitz (r := r / 8) (by positivity)
    (M / (r / 2) / (r / 8)) fun y hy => ?_
  set d := y - x
  have hd : ‖d‖ < r / 8 := by rwa [← dist_eq_norm]
  -- `h u = f (u + d) - f u` is holomorphic near `x` and small
  set h : E → F := fun u => f (u + d) - f u
  set V : Set E := ball x r ∩ (fun u => u + d) ⁻¹' ball x r
  have hV : IsOpen V := isOpen_ball.inter (isOpen_ball.preimage (by fun_prop))
  have hhV : DifferentiableOn ℂ h V := by
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hda _ (ball_subset_closedBall hu.2)).comp u
      (differentiableAt_id.add_const d)).sub (hda u (ball_subset_closedBall hu.1))
  have hbV : closedBall x (r / 8) ⊆ V := by
    intro u hu
    rw [mem_closedBall] at hu
    refine ⟨by rw [mem_ball]; linarith, ?_⟩
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    calc ‖u + d - x‖ = ‖(u - x) + d‖ := by congr 1; abel
      _ ≤ ‖u - x‖ + ‖d‖ := norm_add_le _ _
      _ < r := by rw [← dist_eq_norm]; linarith
  have hhM : ∀ u ∈ closedBall x (r / 8), ‖h u‖ ≤ M / (r / 2) * dist y x := by
    intro u hu
    rw [mem_closedBall] at hu
    have hs : ∀ z ∈ closedBall x (r / 2), DifferentiableAt ℂ f z := fun z hz =>
      hda z (closedBall_subset_closedBall (by linarith) hz)
    have hu1 : u ∈ closedBall x (r / 2) := by rw [mem_closedBall]; linarith
    have hu2 : u + d ∈ closedBall x (r / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖u + d - x‖ = ‖(u - x) + d‖ := by congr 1; abel
        _ ≤ ‖u - x‖ + ‖d‖ := norm_add_le _ _
        _ ≤ r / 2 := by rw [← dist_eq_norm]; linarith
    have := (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_fderiv_le hs hD hu1 hu2
    rw [add_sub_cancel_left] at this
    rw [dist_eq_norm]; exact this
  have key := norm_fderiv_le hV hhV (by positivity : 0 < r / 8) hbV hhM
  have hfd : fderiv ℂ h x = fderiv ℂ f y - fderiv ℂ f x := by
    have h1 : HasFDerivAt (fun u => f (u + d)) (fderiv ℂ f (x + d)) x :=
      (hda _ (by simp [d]; linarith)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const d)
    have h2 : HasFDerivAt h (fderiv ℂ f (x + d) - fderiv ℂ f x) x :=
      h1.sub (hda x (mem_closedBall_self hr.le)).hasFDerivAt
    rw [h2.fderiv]
    simp [d]
  rw [hfd, ← dist_eq_norm] at key
  calc dist (fderiv ℂ f y) (fderiv ℂ f x) ≤ M / (r / 2) * dist y x / (r / 8) := key
    _ = M / (r / 2) / (r / 8) * dist y x := by ring

-- differentiating the Cauchy integral
lemma differentiableAt_fderiv_apply [CompleteSpace F] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) (v : E) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨r, hr, M, hb, hM⟩ := exists_bound hU hf hx
  have hD := norm_fderiv_le_half hU hf hr hb hM
  have hcont := continuousOn_fderiv hU hf
  suffices h : ∀ w : E, ‖w‖ ≤ r / 4 → DifferentiableAt ℂ (fun y => fderiv ℂ f y w) x by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    set t : ℂ := ((r / 4 / ‖v‖ : ℝ) : ℂ)
    have ht : t ≠ 0 := by simp only [t, ne_eq, ofReal_eq_zero]; positivity
    have htv : ‖t • v‖ ≤ r / 4 := by
      rw [norm_smul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp; rfl
    have := (h (t • v) htv).const_smul t⁻¹
    convert this using 2 with y
    rw [Pi.smul_apply, map_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
  intro w hw
  set c := circleMap 0 1
  have hc1 : ∀ θ, ‖c θ‖ = 1 := fun θ => by simp [c]
  have hc0 : ∀ θ, c θ ≠ 0 := fun θ => circleMap_ne_center one_ne_zero
  have hcc : Continuous c := continuous_circleMap 0 1
  set G : E → ℝ → F := fun y θ => (c θ * I) • ((1 / c θ ^ 2) • f (y + c θ • w))
  set G' : E → ℝ → E →L[ℂ] F := fun y θ => (c θ * I * (1 / c θ ^ 2)) • fderiv ℂ f (y + c θ • w)
  have hmem : ∀ y ∈ ball x (r / 4), ∀ θ : ℝ, y + c θ • w ∈ closedBall x (r / 2) := by
    intro y hy θ
    rw [mem_ball] at hy
    rw [mem_closedBall]
    calc dist (y + c θ • w) x ≤ dist (y + c θ • w) y + dist y x := dist_triangle _ _ _
      _ = ‖c θ‖ * ‖w‖ + dist y x := by rw [dist_self_add_left, norm_smul]
      _ ≤ r / 2 := by rw [hc1]; linarith
  have hmemU : ∀ y ∈ ball x (r / 4), ∀ θ : ℝ, y + c θ • w ∈ U := fun y hy θ =>
    hb (closedBall_subset_closedBall (by linarith) (hmem y hy θ))
  have hinv : Continuous fun θ => 1 / c θ ^ 2 :=
    continuous_const.div (hcc.pow 2) fun θ => pow_ne_zero 2 (hc0 θ)
  have hGc : ∀ y ∈ ball x (r / 4), Continuous (G y) := fun y hy =>
    ((hcc.mul continuous_const).smul (hinv.smul
      (hf.continuousOn.comp_continuous (by fun_prop) (hmemU y hy))))
  have hx4 : x ∈ ball x (r / 4) := mem_ball_self (by positivity)
  have hG'c : Continuous (G' x) :=
    ((hcc.mul continuous_const).mul hinv).smul
      (hcont.comp_continuous (by fun_prop) (hmemU x hx4))
  have heq : ∀ y ∈ ball x (r / 4),
      fderiv ℂ f y w = (2 * π * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, G y θ := by
    intro y hy
    have hyb : closedBall y ‖w‖ ⊆ U := by
      intro z hz
      rw [mem_closedBall, mem_ball] at *
      exact hb (by rw [mem_closedBall]; linarith [dist_triangle z y x])
    rw [fderiv_apply_eq_circleIntegral hU hf hyb, circleIntegral]
    simp only [deriv_circleMap, G, c]
  have hint : HasFDerivAt (fun y => ∫ θ in (0 : ℝ)..2 * π, G y θ)
      (∫ θ in (0 : ℝ)..2 * π, G' x θ) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := ball x (r / 4)) (bound := fun _ => M / (r / 2)) (ball_mem_nhds x (by positivity))
      ?_ ((hGc x hx4).intervalIntegrable _ _) hG'c.aestronglyMeasurable ?_
      intervalIntegrable_const ?_
    · filter_upwards [ball_mem_nhds x (by positivity : 0 < r / 4)] with y hy
      exact (hGc y hy).aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ y hy => ?_
      simp only [G', norm_smul, norm_mul, hc1, norm_I, one_div, norm_inv, norm_pow, one_pow,
        inv_one, mul_one, one_mul]
      exact hD _ (hmem y hy θ)
    · refine Eventually.of_forall fun θ _ y hy => ?_
      have h1 : HasFDerivAt (fun y => f (y + c θ • w)) (fderiv ℂ f (y + c θ • w)) y :=
        ((hf _ (hmemU y hy θ)).differentiableAt (hU.mem_nhds (hmemU y hy θ))).hasFDerivAt.comp y
          ((hasFDerivAt_id y).add_const _)
      have h2 := h1.const_smul (c θ * I * (1 / c θ ^ 2))
      have h3 : (fun x => G x θ) = (c θ * I * (1 / c θ ^ 2)) • fun y => f (y + c θ • w) := by
        funext y; simp only [G, Pi.smul_apply, smul_smul]
      rw [h3]; exact h2
  refine ((hint.const_smul (2 * π * I)⁻¹).differentiableAt).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds x (by positivity : 0 < r / 4)] with y hy
  exact heq y hy

lemma clm_eq_sum [FiniteDimensional ℂ E] (L : E →L[ℂ] F) :
    L = ∑ i, ContinuousLinearMap.smulRightL ℂ E F
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ E).coord i))
      (L (Module.finBasis ℂ E i)) := by
  have hs : ∀ (c : StrongDual ℂ E) (w : F) (u : E),
      ContinuousLinearMap.smulRightL ℂ E F c w u = c u • w := fun _ _ _ => rfl
  ext v
  simp only [ContinuousLinearMap.sum_apply, hs, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply]
  conv_lhs => rw [← (Module.finBasis ℂ E).sum_repr v]
  simp only [map_sum, map_smul]

lemma differentiableOn_fderiv [FiniteDimensional ℂ E] [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  intro x hx
  refine DifferentiableAt.differentiableWithinAt ?_
  rw [show fderiv ℂ f = fun y => ∑ i, ContinuousLinearMap.smulRightL ℂ E F
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ E).coord i))
      (fderiv ℂ f y (Module.finBasis ℂ E i)) from funext fun y => clm_eq_sum _]
  exact DifferentiableAt.fun_sum fun i _ =>
    (ContinuousLinearMap.differentiableAt _).comp x
      (differentiableAt_fderiv_apply hU hf hx (Module.finBasis ℂ E i))

lemma differentiableOn_iteratedFDeriv [FiniteDimensional ℂ E] [CompleteSpace F] {f : E → F}
    {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedFDeriv ℂ n f) U := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (LinearIsometryEquiv.differentiable _).comp_differentiableOn hf
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (LinearIsometryEquiv.differentiable _).comp_differentiableOn
      (differentiableOn_fderiv hU ih)

lemma norm_iteratedFDeriv_le [FiniteDimensional ℂ E] [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} {r M : ℝ} (hr : 0 < r)
    (hb : closedBall x r ⊆ U) (hM : ∀ y ∈ closedBall x r, ‖f y‖ ≤ M) (k : ℕ) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ M * (k / r) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [norm_iteratedFDeriv_zero] using hM x (mem_closedBall_self hr.le)
  set δ := r / k
  have hδ : 0 < δ := by positivity
  have key : ∀ j : ℕ, j ≤ k → ∀ y ∈ closedBall x (r - j * δ),
      ‖iteratedFDeriv ℂ j f y‖ ≤ M / δ ^ j := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      simpa [norm_iteratedFDeriv_zero] using hM y (by simpa using hy)
    | succ j ih =>
      intro hj y hy
      have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      have hs : closedBall y δ ⊆ closedBall x (r - j * δ) := by
        intro z hz
        rw [mem_closedBall] at *
        push_cast at hy
        linarith [dist_triangle z y x]
      have hs' : closedBall x (r - j * δ) ⊆ U :=
        (closedBall_subset_closedBall (by nlinarith)).trans hb
      have := norm_fderiv_le hU (differentiableOn_iteratedFDeriv hU hf j) hδ (hs.trans hs')
        fun z hz => ih (by omega) z (hs hz)
      rw [norm_fderiv_iteratedFDeriv] at this
      calc _ ≤ M / δ ^ j / δ := this
        _ = M / δ ^ (j + 1) := by rw [pow_succ, div_div]
  have := key k le_rfl x (mem_closedBall_self (by
    simp only [δ]; field_simp; simp))
  calc _ ≤ M / δ ^ k := this
    _ = M * (k / r) ^ k := by simp only [δ]; rw [div_pow, div_pow]; field_simp

lemma iteratedDeriv_line [FiniteDimensional ℂ E] [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (x y : E) (n : ℕ) :
    ∀ z : ℂ, x + z • y ∈ U →
      iteratedDeriv n (fun w : ℂ => f (x + w • y)) z = iteratedFDeriv ℂ n f (x + z • y) (fun _ => y) := by
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    have hV : IsOpen {w : ℂ | x + w • y ∈ U} := hU.preimage (by fun_prop)
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun w : ℂ => f (x + w • y)) =ᶠ[𝓝 z]
        fun w => iteratedFDeriv ℂ n f (x + w • y) (fun _ => y) := by
      filter_upwards [hV.mem_nhds hz] with w hw
      exact ih w hw
    rw [hev.deriv_eq]
    have h1 := hasDerivAt_line (x := x) (v := y) (z := z)
      ((differentiableOn_iteratedFDeriv hU hf n _ hz).differentiableAt (hU.mem_nhds hz))
    have h2 : HasDerivAt (fun w => iteratedFDeriv ℂ n f (x + w • y) (fun _ => y))
        (fderiv ℂ (iteratedFDeriv ℂ n f) (x + z • y) y (fun _ => y)) z :=
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F
        (fun _ => y)).hasFDerivAt.comp_hasDerivAt z h1
    rw [h2.deriv, iteratedFDeriv_succ_apply_left]
    rfl

theorem analyticAt_of_differentiableOn [FiniteDimensional ℂ E] [CompleteSpace F] {f : E → F}
    {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) :
    AnalyticAt ℂ f x := by
  obtain ⟨r, hr, M, hb, hM⟩ := exists_bound hU hf hx
  have he : 1 < Real.exp 1 := by simpa using Real.add_one_lt_exp one_ne_zero
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set ρ : NNReal := ⟨r / Real.exp 1, by positivity⟩
  have hρ : (ρ : ℝ) = r / Real.exp 1 := rfl
  set p : FormalMultilinearSeries ℂ E F := fun k => ((k.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ k f x
  refine ⟨p, ρ, ?_, ?_, ?_⟩
  · refine p.le_radius_of_bound M fun k => ?_
    have h1 := norm_iteratedFDeriv_le hU hf hr hb hM k
    have h2 : (k : ℝ) ^ k / k.factorial ≤ Real.exp 1 ^ k := by
      rw [Real.exp_one_pow]; exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg k) k
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hr.le))
    calc ‖p k‖ * (ρ : ℝ) ^ k
        = ‖iteratedFDeriv ℂ k f x‖ / k.factorial * (r / Real.exp 1) ^ k := by
          rw [hρ]; simp only [p, norm_smul, norm_inv, Complex.norm_natCast]; ring
      _ ≤ M * (k / r) ^ k / k.factorial * (r / Real.exp 1) ^ k := by gcongr
      _ = M * ((k : ℝ) ^ k / k.factorial / Real.exp 1 ^ k) := by
          rw [div_pow, div_pow]; field_simp
      _ ≤ M * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact h2
      _ = M := mul_one M
  · exact ENNReal.coe_pos.2 (NNReal.coe_pos.1 (by rw [hρ]; positivity))
  · intro y hy
    have hy' : ‖y‖ < r / Real.exp 1 := by
      have h1 : ‖y‖ < ρ := by simpa using hy
      rwa [hρ] at h1
    have hmem : ∀ z : ℂ, ‖z‖ < Real.exp 1 → x + z • y ∈ U := by
      intro z hz
      refine hb (line_mem ?_)
      calc ‖z‖ * ‖y‖ ≤ Real.exp 1 * (r / Real.exp 1) := by gcongr
        _ = r := by field_simp
    have hg : DifferentiableOn ℂ (fun w : ℂ => f (x + w • y)) (ball 0 (Real.exp 1)) := by
      intro z hz
      rw [mem_ball_zero_iff] at hz
      exact (hasDerivAt_line ((hf _ (hmem z hz)).differentiableAt
        (hU.mem_nhds (hmem z hz)))).differentiableAt.differentiableWithinAt
    have h := Complex.hasSum_taylorSeries_on_ball hg (z := 1) (by simpa using he)
    simp only [sub_zero, one_pow, one_smul, one_smul] at h
    convert h using 1
    · funext n
      rw [iteratedDeriv_line hU hf x y n 0 (by simpa using hx), zero_smul, add_zero]
      rfl

end ABC.S4.PeriodMapAux
