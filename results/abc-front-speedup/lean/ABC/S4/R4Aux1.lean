import ABC.S4.Defs
import ABC.S4.FlowHoloAux1

/-! R4 helper: the vector field of `Kbnf` splits as the integrable rotation field plus `J∇R`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R4Aux

-- `J∇K₀`, `K₀ = ν p + b p²`
def F0 (ν b : ℝ) (w : C2) : C2 :=
  ![((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * w 1, -(((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * w 0)]

def P0 (ν b : ℝ) (w : C2) : ℂ := ν / 2 * (w 0 ^ 2 + w 1 ^ 2) + b / 4 * (w 0 ^ 2 + w 1 ^ 2) ^ 2

theorem hasFDerivAt_P0 (ν b : ℝ) (w : C2) :
    HasFDerivAt (P0 ν b) ((((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * w 0) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0
      + (((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * w 1) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1) w := by
  have h0 := hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) w
  have h1 := hasFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) w
  have hq := (h0.pow 2).add (h1.pow 2)
  have := ((hq.const_mul ((ν : ℂ) / 2)).add ((hq.pow 2).const_mul ((b : ℂ) / 4)))
  refine (this.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  · simp
    ring
  · simp [P0]


theorem hamVF_Kbnf {ν b : ℝ} {R : C2 → ℂ → ℂ} {t : ℂ} {w : C2}
    (hR : DifferentiableAt ℂ (fun w => R w t) w) :
    hamVF (fun w => Kbnf ν b R w t) w = F0 ν b w +
      ![fderiv ℂ (fun w => R w t) w (Pi.single 1 1), -fderiv ℂ (fun w => R w t) w (Pi.single 0 1)] := by
  have hK : (fun w => Kbnf ν b R w t) = fun w => P0 ν b w + R w t := by
    funext w; simp [Kbnf, P0]
  have hd := (hasFDerivAt_P0 ν b w).fun_add hR.hasFDerivAt
  rw [hK, hamVF, hd.fderiv]
  ext i
  fin_cases i <;> simp [F0]; ring

theorem isOpen_polydisc (ρ : ℝ) : IsOpen (polydisc ρ) := isOpen_lt continuous_norm continuous_const

theorem isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem differentiableAt_R {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hK : IsTPHam (Kbnf ν b R) ρ s)
    {t : ℂ} (ht : t ∈ strip s) {w : C2} (hw : w ∈ polydisc ρ) :
    DifferentiableAt ℂ (fun w => R w t) w := by
  have h1 : DifferentiableAt ℂ (fun q : C2 × ℂ => Kbnf ν b R q.1 q.2) (w, t) :=
    hK.holo.differentiableAt (((isOpen_polydisc ρ).prod (isOpen_strip s)).mem_nhds ⟨hw, ht⟩)
  have h2 : DifferentiableAt ℂ (fun w => Kbnf ν b R w t) w :=
    h1.comp (f := fun w : C2 => (w, t)) w ((differentiableAt_id).prodMk (differentiableAt_const t))
  have h3 : DifferentiableAt ℂ (P0 ν b) w := (hasFDerivAt_P0 ν b w).differentiableAt
  have e : (fun w => R w t) = fun w => Kbnf ν b R w t - P0 ν b w := by
    funext w; simp [Kbnf, P0]
  rw [e]
  exact h2.sub h3

theorem differentiableOn_R {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hK : IsTPHam (Kbnf ν b R) ρ s)
    {t : ℂ} (ht : t ∈ strip s) : DifferentiableOn ℂ (fun w => R w t) (polydisc ρ) :=
  fun _ hw => (differentiableAt_R hK ht hw).differentiableWithinAt

theorem Bound.nonneg {R : C2 → ℂ → ℂ} {ρ s C : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hR : Bound R ρ s C 5) : 0 ≤ C := by
  set w : C2 := fun _ => ((ρ / 2 : ℝ) : ℂ)
  have hw : ‖w‖ = ρ / 2 := by
    simp only [w]
    rw [pi_norm_const, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := hR w (by simp only [polydisc, mem_ofPred_eq, hw]; linarith) 0 (by simp [strip, hs])
  rw [hw] at h
  by_contra hC
  have : C * (ρ / 2) ^ 5 < 0 := mul_neg_of_neg_of_pos (not_le.1 hC) (by positivity)
  linarith [norm_nonneg (R w 0)]

theorem R_zero {R : C2 → ℂ → ℂ} {ρ s C : ℝ} (hρ : 0 < ρ) (hR : Bound R ρ s C 5) {t : ℂ}
    (ht : t ∈ strip s) : R 0 t = 0 := by
  have h := hR 0 (by simp [polydisc, hρ]) t ht
  simpa using h

/-- Cauchy: `‖∇R‖ ≤ 32 C ‖w‖⁴` on `polydisc (ρ/2)`. -/
theorem norm_fderiv_R_le {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} (hρ : 0 < ρ) (hs : 0 < s)
    (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) {t : ℂ} (ht : t ∈ strip s) {w : C2}
    (hw : ‖w‖ < ρ / 2) : ‖fderiv ℂ (fun w => R w t) w‖ ≤ 32 * C * ‖w‖ ^ 4 := by
  have hC := Bound.nonneg hρ hs hR
  have hD := differentiableOn_R hK ht
  -- radius `δ ∈ (0, ρ/2)` around `w`, with `‖w‖ ≤ δ`
  have key : ∀ δ, 0 < δ → ‖w‖ ≤ δ → δ < ρ / 2 →
      ‖fderiv ℂ (fun w => R w t) w‖ ≤ C * (2 * δ) ^ 5 / δ := by
    intro δ hδ hwδ hδρ
    refine ABC.S4.FlowHoloAux.norm_fderiv_le_of_closedBall (isOpen_polydisc ρ) hD hδ
      (by positivity) ?_ ?_
    · intro z hz
      have : ‖z‖ ≤ 2 * δ := by
        have := norm_le_norm_add_norm_sub' z w
        rw [mem_closedBall, dist_eq_norm] at hz
        linarith
      simp only [polydisc, mem_ofPred_eq]
      linarith
    · intro z hz
      have hz' : ‖z‖ ≤ 2 * δ := by
        have := norm_le_norm_add_norm_sub' z w
        rw [mem_closedBall, dist_eq_norm] at hz
        linarith
      calc ‖R z t‖ ≤ C * ‖z‖ ^ 5 := hR z (by simp only [polydisc, mem_ofPred_eq]; linarith) t ht
        _ ≤ C * (2 * δ) ^ 5 := by gcongr
  rcases eq_or_ne w 0 with rfl | hw0
  · -- let `δ → 0`
    have ht : Tendsto (fun δ : ℝ => 32 * C * δ ^ 4) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => 32 * C * δ ^ 4) (𝓝 0) (𝓝 (32 * C * 0 ^ 4)) :=
        (continuous_const.mul (continuous_pow 4)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖fderiv ℂ (fun w => R w t) 0‖ ≤ 32 * C * δ ^ 4 := by
      have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ρ / 2 :=
        nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
      filter_upwards [h1, self_mem_nhdsWithin] with δ hδ hδ0
      have hδ0' : (0 : ℝ) < δ := hδ0
      have := key δ hδ0' (by simpa using hδ0'.le) hδ
      calc _ ≤ C * (2 * δ) ^ 5 / δ := this
        _ = 32 * C * δ ^ 4 := by field_simp; ring
    have := ge_of_tendsto ht hev
    simpa using this
  · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    calc _ ≤ C * (2 * ‖w‖) ^ 5 / ‖w‖ := key ‖w‖ hpos le_rfl hw
      _ = 32 * C * ‖w‖ ^ 4 := by field_simp; ring

theorem F0_coord_lip {ν b r : ℝ} {w w' : C2} (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r) (x x' : ℂ)
    (hx : ‖x - x'‖ ≤ ‖w - w'‖) (hx' : ‖x'‖ ≤ r) :
    ‖((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * x - ((ν : ℂ) + b * (w' 0 ^ 2 + w' 1 ^ 2)) * x'‖ ≤
      (|ν| + 6 * |b| * r ^ 2) * ‖w - w'‖ := by
  set d := ‖w - w'‖
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  have h0 : ‖w 0‖ ≤ r := (norm_le_pi_norm w 0).trans hw
  have h1 : ‖w 1‖ ≤ r := (norm_le_pi_norm w 1).trans hw
  have h0' : ‖w' 0‖ ≤ r := (norm_le_pi_norm w' 0).trans hw'
  have h1' : ‖w' 1‖ ≤ r := (norm_le_pi_norm w' 1).trans hw'
  have d0 : ‖w 0 - w' 0‖ ≤ d := by simpa using norm_le_pi_norm (w - w') 0
  have d1 : ‖w 1 - w' 1‖ ≤ d := by simpa using norm_le_pi_norm (w - w') 1
  have hd : 0 ≤ d := norm_nonneg _
  have e : ((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * x - ((ν : ℂ) + b * (w' 0 ^ 2 + w' 1 ^ 2)) * x' =
      ((ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)) * (x - x') +
        b * ((w 0 - w' 0) * (w 0 + w' 0) + (w 1 - w' 1) * (w 1 + w' 1)) * x' := by ring
  have hA : ‖(ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)‖ ≤ |ν| + |b| * (2 * r ^ 2) := by
    calc _ ≤ ‖(ν : ℂ)‖ + ‖(b : ℂ)‖ * (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_pow, norm_pow])
      _ ≤ |ν| + |b| * (r ^ 2 + r ^ 2) := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
      _ = _ := by ring
  have hB : ‖(w 0 - w' 0) * (w 0 + w' 0) + (w 1 - w' 1) * (w 1 + w' 1)‖ ≤ 4 * r * d := by
    calc _ ≤ ‖w 0 - w' 0‖ * (‖w 0‖ + ‖w' 0‖) + ‖w 1 - w' 1‖ * (‖w 1‖ + ‖w' 1‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr <;> exact norm_add_le _ _
      _ ≤ d * (r + r) + d * (r + r) := by gcongr
      _ = _ := by ring
  rw [e]
  calc _ ≤ ‖(ν : ℂ) + b * (w 0 ^ 2 + w 1 ^ 2)‖ * ‖x - x'‖ +
        ‖(b : ℂ)‖ * ‖(w 0 - w' 0) * (w 0 + w' 0) + (w 1 - w' 1) * (w 1 + w' 1)‖ * ‖x'‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (|ν| + |b| * (2 * r ^ 2)) * d + |b| * (4 * r * d) * r := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        gcongr
    _ = _ := by ring

theorem F0_lip {ν b r : ℝ} {w w' : C2} (hw : ‖w‖ ≤ r) (hw' : ‖w'‖ ≤ r) :
    ‖F0 ν b w - F0 ν b w'‖ ≤ (|ν| + 6 * |b| * r ^ 2) * ‖w - w'‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hw
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have d0 : ‖w 0 - w' 0‖ ≤ ‖w - w'‖ := by simpa using norm_le_pi_norm (w - w') 0
  have d1 : ‖w 1 - w' 1‖ ≤ ‖w - w'‖ := by simpa using norm_le_pi_norm (w - w') 1
  fin_cases i
  · simpa [F0] using F0_coord_lip hw hw' (w 1) (w' 1) d1 ((norm_le_pi_norm w' 1).trans hw')
  · have := F0_coord_lip (ν := ν) (b := b) hw hw' (w 0) (w' 0) d0 ((norm_le_pi_norm w' 0).trans hw')
    simp only [F0, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.sub_apply]
    rw [← norm_neg]
    convert this using 2
    ring

def om (ν b : ℝ) (x : E 2) : ℝ := ν + b * (x 0 ^ 2 + x 1 ^ 2)

-- the exact solution of `K₀` from the real point `x` (clockwise rotation)
def g0 (ν b : ℝ) (x : E 2) (t : ℝ) : C2 :=
  ![((x 0 * Real.cos (om ν b x * t) + x 1 * Real.sin (om ν b x * t) : ℝ) : ℂ),
    ((-(x 0 * Real.sin (om ν b x * t)) + x 1 * Real.cos (om ν b x * t) : ℝ) : ℂ)]

theorem g0_sq (x0 x1 θ : ℝ) :
    (x0 * Real.cos θ + x1 * Real.sin θ) ^ 2 + (-(x0 * Real.sin θ) + x1 * Real.cos θ) ^ 2 =
      x0 ^ 2 + x1 ^ 2 := by
  linear_combination (x0 ^ 2 + x1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem g0_zero (ν b : ℝ) (x : E 2) : g0 ν b x 0 = ofR x := by
  ext i; fin_cases i <;> simp [g0, ofR]

theorem hasDerivAt_g0 (ν b : ℝ) (x : E 2) (t : ℝ) :
    HasDerivAt (g0 ν b x) (F0 ν b (g0 ν b x t)) t := by
  set ω := om ν b x with hω
  have hθ : HasDerivAt (fun t => ω * t) ω t := by simpa using (hasDerivAt_id t).const_mul ω
  have hsq : ((x 0 * Real.cos (ω * t) + x 1 * Real.sin (ω * t) : ℝ) : ℂ) ^ 2 +
      ((-(x 0 * Real.sin (ω * t)) + x 1 * Real.cos (ω * t) : ℝ) : ℂ) ^ 2 =
        ((x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2) := by
    exact_mod_cast g0_sq (x 0) (x 1) (ω * t)
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · have h := (((hθ.cos).const_mul (x 0)).add ((hθ.sin).const_mul (x 1))).ofReal_comp
    convert h using 1
    · funext y; simp [g0, hω]
    · simp only [g0, F0, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [hsq, hω, om]
      push_cast
      ring
  · have h := (((hθ.sin).const_mul (x 0)).neg.add ((hθ.cos).const_mul (x 1))).ofReal_comp
    convert h using 1
    · funext y; simp [g0, hω]
    · simp only [g0, F0, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [hsq, hω, om]
      push_cast
      ring

theorem norm_g0_le (ν b : ℝ) (x : E 2) (t : ℝ) : ‖g0 ν b x t‖ ≤ ‖x‖ := by
  have hx : ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [hx]
  set θ := om ν b x * t
  fin_cases i
  · simp only [g0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Complex.norm_real,
      Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    nlinarith [g0_sq (x 0) (x 1) θ, sq_nonneg (-(x 0 * Real.sin θ) + x 1 * Real.cos θ)]
  · simp only [g0, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Complex.norm_real, Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    nlinarith [g0_sq (x 0) (x 1) θ, sq_nonneg (x 0 * Real.cos θ + x 1 * Real.sin θ)]

theorem norm_ofR_le (x : E 2) : ‖ofR x‖ ≤ ‖x‖ := by
  simpa [g0_zero] using norm_g0_le 0 0 x 0

theorem norm_JgradR_le (f : C2 →L[ℂ] ℂ) : ‖(![f (Pi.single 1 1), -f (Pi.single 0 1)] : C2)‖ ≤ ‖f‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [Pi.norm_single] using f.le_opNorm (Pi.single 1 1)
  · simpa [Pi.norm_single] using f.le_opNorm (Pi.single 0 1)

-- Lipschitz constant of `F0` on `‖w‖ ≤ 1`, and the Gronwall factor over one period
def Lc (ν b : ℝ) : ℝ := |ν| + 6 * |b| + 1

def Gc (ν b : ℝ) : ℝ := (Real.exp (2 * π * Lc ν b) - 1) / Lc ν b

theorem Lc_pos (ν b : ℝ) : 0 < Lc ν b := by unfold Lc; positivity

theorem Gc_nonneg (ν b : ℝ) : 0 ≤ Gc ν b := by
  unfold Gc
  have := Lc_pos ν b
  have : 1 ≤ Real.exp (2 * π * Lc ν b) := Real.one_le_exp (by positivity)
  exact div_nonneg (by linarith) (Lc_pos ν b).le

/-- Gronwall against the exact rotation `g0`. -/
theorem gron_step {ν b r ε T : ℝ} (hr1 : r ≤ 1) (hε : 0 ≤ ε) {γ V : ℝ → C2} {x : E 2}
    (hT : 0 ≤ T) (hT2 : T ≤ 2 * π)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (V t) (Icc 0 T) t)
    (hV : ∀ t ∈ Ico 0 T, ‖V t - F0 ν b (γ t)‖ ≤ ε)
    (hγr : ∀ t ∈ Ico 0 T, ‖γ t‖ ≤ r) (hx : ‖x‖ ≤ r) (h0 : γ 0 = ofR x) :
    ‖γ T - g0 ν b x T‖ ≤ ε * Gc ν b := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hL := Lc_pos ν b
  set K : NNReal := ⟨Lc ν b, hL.le⟩
  have hlip : ∀ t ∈ Ico 0 T, LipschitzOnWith K ((fun _ : ℝ => F0 ν b) t)
      ((fun _ : ℝ => closedBall (0 : C2) r) t) := by
    intro _ _
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
    rw [mem_closedBall, dist_zero_right] at hw hw'
    rw [dist_eq_norm, dist_eq_norm]
    refine (F0_lip hw hw').trans ?_
    have : r ^ 2 ≤ 1 := by nlinarith
    have : |ν| + 6 * |b| * r ^ 2 ≤ Lc ν b := by
      unfold Lc; nlinarith [abs_nonneg b]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hcont : ContinuousOn γ (Icc 0 T) := fun t ht => (hγ t ht).continuousWithinAt
  have h := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => F0 ν b)
    (s := fun _ => closedBall (0 : C2) r) (K := K) (f' := V) (g := g0 ν b x)
    (g' := fun t => F0 ν b (g0 ν b x t)) (εf := ε) (εg := 0) (δ := 0) hlip hcont
    (fun t ht => ((hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))).mono
        (fun _ h => h))
    (fun t ht => by rw [dist_eq_norm]; exact hV t ht)
    (fun t ht => by rw [mem_closedBall, dist_zero_right]; exact hγr t ht)
    (fun t _ => (hasDerivAt_g0 ν b x t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_g0 ν b x t).hasDerivWithinAt)
    (fun t _ => by simp)
    (fun t _ => by rw [mem_closedBall, dist_zero_right]; exact (norm_g0_le ν b x t).trans hx)
    (by rw [h0, g0_zero, dist_self]) T ⟨hT, le_rfl⟩
  rw [dist_eq_norm, sub_zero, add_zero, gronwallBound_of_K_ne_0 (by simp [K]; exact hL.ne')]
    at h
  simp only [zero_mul, zero_add] at h
  change _ ≤ ε / Lc ν b * (Real.exp (Lc ν b * T) - 1) at h
  refine h.trans ?_
  calc ε / Lc ν b * (Real.exp (Lc ν b * T) - 1)
      ≤ ε / Lc ν b * (Real.exp (2 * π * Lc ν b) - 1) := by
        have : Real.exp (Lc ν b * T) ≤ Real.exp (2 * π * Lc ν b) := Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hε hL.le)
    _ = ε * Gc ν b := by rw [Gc]; ring

end ABC.S4.R4Aux
