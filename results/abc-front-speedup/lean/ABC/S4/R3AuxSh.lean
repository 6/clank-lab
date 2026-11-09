import ABC.S4.R3Aux0

/-! R3 auxiliaries: one polynomial shear step, and composition of conjugacies. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

lemma sh_isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma sh_isOpen_polydisc (ρ : ℝ) : IsOpen (polydisc ρ) :=
  isOpen_lt continuous_norm continuous_const

lemma sh_polydisc_eq_ball (ρ : ℝ) : polydisc ρ = ball (0 : C2) ρ := by
  ext w; simp [polydisc]

lemma sh_ofReal_mem_strip {s : ℝ} (hs : 0 < s) (x : ℝ) : (x : ℂ) ∈ strip s := by
  simp [strip, hs]

lemma clm_C2 (L : C2 →L[ℂ] ℂ) (v : C2) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) := by
  have : v = v 0 • (Pi.single 0 1 : C2) + v 1 • (Pi.single 1 1 : C2) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]


/-! ### the shear as a vector map -/

def shJ (u : Fin 2 → ℝ) : C2 := ![(u 1 : ℂ), -(u 0 : ℂ)]

def linL (u : Fin 2 → ℝ) : C2 →L[ℂ] ℂ :=
  (u 0 : ℂ) • ContinuousLinearMap.proj 0 + (u 1 : ℂ) • ContinuousLinearMap.proj 1

lemma linL_apply (u : Fin 2 → ℝ) (w : C2) : linL u w = lin u w := by
  simp [linL, lin]

lemma linL_single (u : Fin 2 → ℝ) (j : Fin 2) : linL u (Pi.single j 1) = u j := by
  fin_cases j <;> simp [linL]

lemma shear_eq (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (t : ℂ) (w : C2) :
    shear k u c t w = w + (k * c t * lin u w ^ (k - 1)) • shJ u := by
  ext i; fin_cases i <;> simp [shear, shJ] <;> ring

lemma hasFDerivAt_lin (u : Fin 2 → ℝ) (w : C2) : HasFDerivAt (lin u) (linL u) w := by
  have := (linL u).hasFDerivAt (x := w)
  have e : (⇑(linL u)) = lin u := funext (linL_apply u)
  rwa [e] at this

lemma hasFDerivAt_lin_pow (u : Fin 2 → ℝ) (n : ℕ) (w : C2) :
    HasFDerivAt (fun w => lin u w ^ n) ((n * lin u w ^ (n - 1)) • linL u) w := by
  simpa [nsmul_eq_mul] using (hasFDerivAt_lin u w).pow n

lemma hasFDerivAt_shear (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (t : ℂ) (w : C2) :
    HasFDerivAt (shear k u c t)
      (ContinuousLinearMap.id ℂ C2 +
        (((k : ℂ) * c t) • (((k - 1 : ℕ) : ℂ) * lin u w ^ (k - 1 - 1)) • linL u).smulRight
          (shJ u)) w := by
  have e : shear k u c t = fun w => w + (k * c t * lin u w ^ (k - 1)) • shJ u :=
    funext (shear_eq k u c t)
  rw [e]
  exact (hasFDerivAt_id w).add
    (((hasFDerivAt_lin_pow u (k - 1) w).const_mul ((k : ℂ) * c t)).smul_const (shJ u))

/-- the partial derivatives of the transformed Hamiltonian -/
lemma shearK_fderiv_apply (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (K : C2 → ℂ → ℂ) (t : ℂ) (w : C2)
    (hF : DifferentiableAt ℂ (fun w => K w t) (shear k u c t w)) (j : Fin 2) :
    fderiv ℂ (fun w => shearK k u c K w t) w (Pi.single j 1) =
      fderiv ℂ (fun w => K w t) (shear k u c t w) (Pi.single j 1) +
        ((k : ℂ) * c t * (((k - 1 : ℕ) : ℂ) * lin u w ^ (k - 1 - 1)) *
            (u 1 * fderiv ℂ (fun w => K w t) (shear k u c t w) (Pi.single 0 1) -
              u 0 * fderiv ℂ (fun w => K w t) (shear k u c t w) (Pi.single 1 1)) -
          deriv c t * ((k : ℂ) * lin u w ^ (k - 1))) * u j := by
  have h1 := hF.hasFDerivAt.comp w (hasFDerivAt_shear k u c t w)
  have h2 := (hasFDerivAt_lin_pow u k w).const_mul (deriv c t)
  have h3 := h1.sub h2
  have e : (fun w => shearK k u c K w t) =
      ((fun w => K w t) ∘ shear k u c t) - fun w => deriv c t * lin u w ^ k := by
    funext w; simp [shearK]
  rw [e, h3.fderiv]
  set L := fderiv ℂ (fun w => K w t) (shear k u c t w)
  have hJ : L (shJ u) = u 1 * L (Pi.single 0 1) - u 0 * L (Pi.single 1 1) := by
    rw [clm_C2 L (shJ u)]; simp [shJ]; ring
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    map_add, map_smul, linL_single, hJ]
  ring

/-- solution correspondence for one shear -/
lemma shear_sol {k : ℕ} {u : Fin 2 → ℝ} {c : ℂ → ℂ} {K : C2 → ℂ → ℂ} {γ : ℝ → C2} {a b : ℝ}
    (hγ : Solves (shearK k u c K) γ a b)
    (hK : ∀ t ∈ Icc a b, DifferentiableAt ℂ (fun w => K w (t : ℂ)) (shear k u c t (γ t)))
    (hc : ∀ t ∈ Icc a b, DifferentiableAt ℂ c (t : ℂ)) :
    Solves K (fun t => shear k u c t (γ t)) a b := by
  intro t ht
  have hγt := hasDerivWithinAt_pi.1 (hγ t ht)
  have h0 := hγt 0
  have h1 := hγt 1
  simp only [hamVF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    shearK_fderiv_apply k u c K t (γ t) (hK t ht)] at h0 h1
  have hct : HasDerivAt (fun x : ℝ => c x) (deriv c t) t := (hc t ht).hasDerivAt.comp_ofReal
  set L := fderiv ℂ (fun w => K w (t : ℂ)) (shear k u c t (γ t))
  have hlin : HasDerivWithinAt (fun y => lin u (γ y)) ((u 0 : ℂ) * _ + (u 1 : ℂ) * _)
      (Icc a b) t := (h0.const_mul (u 0 : ℂ)).add (h1.const_mul (u 1 : ℂ))
  have hl := hlin.fun_pow (k - 1)
  have hm := (hct.hasDerivWithinAt.const_mul (k : ℂ)).mul hl
  rw [hasDerivWithinAt_pi]
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · have := h0.add (hm.mul_const (u 1 : ℂ))
    refine HasDerivWithinAt.congr_deriv this ?_
    simp only [hamVF, Matrix.cons_val_zero]
    ring
  · have := h1.sub (hm.mul_const (u 0 : ℂ))
    refine HasDerivWithinAt.congr_deriv this ?_
    simp only [hamVF, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

/-! ### holomorphy, reality, periodicity -/

lemma sh_deriv_holo {c : ℂ → ℂ} {s : ℝ} (hc : DifferentiableOn ℂ c (strip s)) :
    DifferentiableOn ℂ (deriv c) (strip s) :=
  hc.deriv (sh_isOpen_strip s)

lemma shear_diffAt {k : ℕ} {u : Fin 2 → ℝ} {c : ℂ → ℂ} {q : ℂ × C2}
    (hc : DifferentiableAt ℂ c q.1) :
    DifferentiableAt ℂ (fun q : ℂ × C2 => shear k u c q.1 q.2) q := by
  have hc' : DifferentiableAt ℂ (fun q : ℂ × C2 => c q.1) q :=
    hc.comp q differentiableAt_fst
  rw [differentiableAt_pi]
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simp only [shear, lin, Matrix.cons_val_zero]
    fun_prop
  · simp only [shear, lin, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    fun_prop

lemma shear_holo {k : ℕ} {u : Fin 2 → ℝ} {c : ℂ → ℂ} {s : ℝ}
    (hc : DifferentiableOn ℂ c (strip s)) (T : Set C2) :
    DifferentiableOn ℂ (fun q : ℂ × C2 => shear k u c q.1 q.2) (strip s ×ˢ T) := by
  intro q hq
  exact (shear_diffAt (hc.differentiableAt ((sh_isOpen_strip s).mem_nhds hq.1))).differentiableWithinAt

lemma sh_deriv_real {c : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hc : DifferentiableOn ℂ c (strip s))
    (hre : ∀ x : ℝ, (c x).im = 0) (x : ℝ) : (deriv c x).im = 0 := by
  have h1 : HasDerivAt (fun y : ℝ => c y) (deriv c x) x :=
    (hc.differentiableAt ((sh_isOpen_strip s).mem_nhds (sh_ofReal_mem_strip hs x))).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (c y).im) (deriv c x).im x := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1
    exact this
  have h3 : (fun y : ℝ => (c y).im) = fun _ => 0 := funext hre
  rw [h3] at h2
  exact (h2.unique (hasDerivAt_const x 0))

lemma sh_deriv_per {c : ℂ → ℂ} (hper : ∀ t, c (t + 2 * π) = c t) (t : ℂ) :
    deriv c (t + 2 * π) = deriv c t := by
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hper

lemma sh_real_of_im {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])

lemma shear_real {k : ℕ} {u : Fin 2 → ℝ} {c : ℂ → ℂ} (hre : ∀ x : ℝ, (c x).im = 0)
    (x : E 2) (t : ℝ) : ∃ y : E 2, shear k u c t (ofR x) = ofR y := by
  refine ⟨!₂[x 0 + k * (c t).re * (u 0 * x 0 + u 1 * x 1) ^ (k - 1) * u 1,
    x 1 - k * (c t).re * (u 0 * x 0 + u 1 * x 1) ^ (k - 1) * u 0], ?_⟩
  have hc := sh_real_of_im (hre t)
  funext i
  fin_cases i
  · simp only [shear, lin, ofR]
    rw [hc]
    simp
  · simp only [shear, lin, ofR]
    rw [hc]
    simp

lemma shear_per {k : ℕ} {u : Fin 2 → ℝ} {c : ℂ → ℂ} (hper : ∀ t, c (t + 2 * π) = c t)
    (t : ℂ) (w : C2) : shear k u c (t + 2 * π) w = shear k u c t w := by
  simp only [shear, hper]

lemma shear_zero {k : ℕ} (hk : 2 ≤ k) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (t : ℂ) :
    shear k u c t 0 = 0 := by
  have : k - 1 ≠ 0 := by omega
  funext i; fin_cases i <;> simp [shear, lin, this]

lemma shear_lin {k : ℕ} (hk : 3 ≤ k) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (t : ℂ) :
    HasFDerivAt (shear k u c t) (ContinuousLinearMap.id ℂ C2) 0 := by
  have : k - 1 - 1 ≠ 0 := by omega
  convert hasFDerivAt_shear k u c t 0 using 1
  ext v i
  simp [lin, this]

/-! ### norm estimates -/

lemma sh_norm_lin {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2) (w : C2) :
    ‖lin u w‖ ≤ 4 * ‖w‖ := by
  have h0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have h1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  calc ‖lin u w‖ ≤ ‖(u 0 : ℂ) * w 0‖ + ‖(u 1 : ℂ) * w 1‖ := norm_add_le _ _
    _ = |u 0| * ‖w 0‖ + |u 1| * ‖w 1‖ := by simp
    _ ≤ 2 * ‖w‖ + 2 * ‖w‖ := by gcongr
    _ = 4 * ‖w‖ := by ring

lemma sh_norm_J {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2) : ‖shJ u‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i <;> simpa [shJ]

lemma shear_sub_norm {k : ℕ} {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2) {c : ℂ → ℂ}
    {B : ℝ} {t : ℂ} (hB : ‖c t‖ ≤ B) (w : C2) :
    ‖shear k u c t w - w‖ ≤ (k * B * 4 ^ (k - 1) * 2) * ‖w‖ ^ (k - 1) := by
  rw [shear_eq, add_sub_cancel_left, norm_smul, norm_mul, norm_mul, norm_pow]
  have hl := sh_norm_lin hu0 hu1 w
  have hJ := sh_norm_J hu0 hu1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  calc ‖(k : ℂ)‖ * ‖c t‖ * ‖lin u w‖ ^ (k - 1) * ‖shJ u‖
      ≤ k * B * (4 * ‖w‖) ^ (k - 1) * 2 := by
        simp only [Complex.norm_natCast]
        gcongr
    _ = (k * B * 4 ^ (k - 1) * 2) * ‖w‖ ^ (k - 1) := by rw [mul_pow]; ring

lemma sh_norm_q2 (v : C2) : ‖q2 v‖ ≤ 2 * ‖v‖ ^ 2 := by
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
  calc ‖q2 v‖ ≤ ‖v 0 ^ 2‖ + ‖v 1 ^ 2‖ := norm_add_le _ _
    _ = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by simp [norm_pow]
    _ ≤ ‖v‖ ^ 2 + ‖v‖ ^ 2 := by gcongr
    _ = 2 * ‖v‖ ^ 2 := by ring

/-- the Schwarz-lemma step -/
lemma sh_schwarz {G : C2 → ℂ} {R A : ℝ} (hA : 0 ≤ A) (hG : DifferentiableOn ℂ G (polydisc R))
    (hb : ∀ x ∈ polydisc R, ‖G x‖ ≤ A * ‖x‖ ^ 3) {w v : C2} (hw : 2 * ‖w‖ < R)
    (hv : ‖v‖ < ‖w‖) : ‖G (w + v) - G w‖ ≤ 16 * A * ‖w‖ ^ 2 * ‖v‖ := by
  have hw0 : 0 < ‖w‖ := (norm_nonneg v).trans_lt hv
  have hsub : ∀ x ∈ ball w ‖w‖, ‖x‖ < 2 * ‖w‖ := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖(x - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
      _ < 2 * ‖w‖ := by linarith
  have hball : ball w ‖w‖ ⊆ polydisc R := fun x hx => by
    show ‖x‖ < R
    linarith [hsub x hx]
  have hwR : w ∈ polydisc R := by show ‖w‖ < R; linarith
  have hmaps : MapsTo G (ball w ‖w‖) (closedBall (G w) (16 * A * ‖w‖ ^ 3)) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb x (hball hx)
    have h2 := hb w hwR
    have h3 : ‖x‖ ^ 3 ≤ (2 * ‖w‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hsub x hx).le 3
    calc ‖G x - G w‖ ≤ ‖G x‖ + ‖G w‖ := norm_sub_le _ _
      _ ≤ A * (2 * ‖w‖) ^ 3 + A * ‖w‖ ^ 3 := by gcongr; exact h1.trans (by gcongr)
      _ ≤ 16 * A * ‖w‖ ^ 3 := by nlinarith [pow_pos hw0 3]
  have hz : w + v ∈ ball w ‖w‖ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hv
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hG.mono hball) hmaps hz
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
  calc ‖G (w + v) - G w‖ ≤ 16 * A * ‖w‖ ^ 3 / ‖w‖ * ‖v‖ := this
    _ = 16 * A * ‖w‖ ^ 2 * ‖v‖ := by field_simp

/-! ### assembling the shear step -/

lemma sh_K_diffAt {K : C2 → ℂ → ℂ} {R s : ℝ} (hK : IsTPHam K R s) {t : ℂ} (ht : t ∈ strip s)
    {w : C2} (hw : w ∈ polydisc R) : DifferentiableAt ℂ (fun w => K w t) w := by
  have h := hK.holo.differentiableAt
    (((sh_isOpen_polydisc R).prod (sh_isOpen_strip s)).mem_nhds (x := (w, t)) ⟨hw, ht⟩)
  have hg : DifferentiableAt ℂ (fun x : C2 => (x, t)) w :=
    differentiableAt_id.prodMk (differentiableAt_const t)
  exact h.comp (g := fun q : C2 × ℂ => K q.1 q.2) w hg

lemma sh_G_holo {K : C2 → ℂ → ℂ} {R s : ℝ} (hK : IsTPHam K R s) {t : ℂ} (ht : t ∈ strip s)
    (ν : ℝ) : DifferentiableOn ℂ (fun x => K x t - ν / 2 * q2 x) (polydisc R) := by
  intro x hx
  have h1 := sh_K_diffAt hK ht hx
  have h2 : DifferentiableAt ℂ (fun x : C2 => (ν : ℂ) / 2 * q2 x) x := by
    simp only [q2]; fun_prop
  exact (h1.sub h2).differentiableWithinAt

lemma sh_identity (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (K : C2 → ℂ → ℂ) (ν : ℝ) (w : C2)
    (t : ℂ) : shearK k u c K w t - K w t - shX k u c ν w t =
      ((K (shear k u c t w) t - ν / 2 * q2 (shear k u c t w)) - (K w t - ν / 2 * q2 w)) +
        ν / 2 * q2 (shear k u c t w - w) := by
  set S := shear k u c t w with hS
  have hS0 : S 0 = w 0 + k * c t * lin u w ^ (k - 1) * u 1 := by simp [hS, shear]
  have hS1 : S 1 = w 1 - k * c t * lin u w ^ (k - 1) * u 0 := by simp [hS, shear]
  simp only [shearK, shX, q2, Pi.sub_apply, hS0, hS1]
  ring

lemma shear_small {k : ℕ} (hk : 3 ≤ k) {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2)
    {c : ℂ → ℂ} {B R : ℝ} (hR1 : R ≤ 1) {t : ℂ} (hB : ‖c t‖ ≤ B) {w : C2}
    (hw : ‖w‖ < min (R / 4) (1 / (2 * (k * B * 4 ^ (k - 1) * 2) + 2))) :
    ‖shear k u c t w - w‖ ≤ ‖w‖ / 2 := by
  set D := (k * B * 4 ^ (k - 1) * 2 : ℝ) with hD
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hD0 : 0 ≤ D := by positivity
  set ρ := ‖w‖
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρ1 : ρ < R / 4 := hw.trans_le (min_le_left _ _)
  have hρ2 : ρ < 1 / (2 * D + 2) := hw.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hρ2
  have hρ3 : ρ ≤ 1 := by linarith
  have h1 := shear_sub_norm (k := k) hu0 hu1 hB w
  have h2 : ρ ^ (k - 1) ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0 hρ3 (by omega)
  calc ‖shear k u c t w - w‖ ≤ D * ρ ^ (k - 1) := h1
    _ ≤ D * ρ ^ 2 := by gcongr
    _ ≤ ρ / 2 := by nlinarith

/-- one shear step: holomorphy, reality, periodicity, the solution correspondence, and the
first-order change of the Hamiltonian -/
theorem shear_step {k : ℕ} (hk : 3 ≤ k) {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2)
    {c : ℂ → ℂ} {K : C2 → ℂ → ℂ} {ν R s A B : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hs : 0 < s)
    (hc : CoefFn c s) (hcB : ∀ t ∈ strip s, ‖c t‖ ≤ B ∧ ‖deriv c t‖ ≤ B)
    (hK : IsTPHam K R s) (hb : Bound (fun w t => K w t - ν / 2 * q2 w) R s A 3) :
    ∃ r > 0, r ≤ R ∧ IsTPHam (shearK k u c K) r s ∧
      IsConj (shearK k u c K) K (shear k u c) r R s ∧
      ∃ C, Bound (fun w t => shearK k u c K w t - K w t - shX k u c ν w t) r s C (k + 1) := by
  have h0s : (0 : ℂ) ∈ strip s := by simpa using sh_ofReal_mem_strip hs 0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hcB 0 h0s).1
  set D := (k * B * 4 ^ (k - 1) * 2 : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  set r := min (R / 4) (1 / (2 * D + 2)) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hrR : r ≤ R / 4 := min_le_left _ _
  have hsmall : ∀ t ∈ strip s, ∀ w ∈ polydisc r, ‖shear k u c t w - w‖ ≤ ‖w‖ / 2 :=
    fun t ht w hw => shear_small hk hu0 hu1 hR1 (hcB t ht).1 hw
  have hmaps : ∀ t ∈ strip s, ∀ w ∈ polydisc r, shear k u c t w ∈ polydisc R := by
    intro t ht w hw
    have h1 := hsmall t ht w hw
    have hw' : ‖w‖ < r := hw
    show ‖shear k u c t w‖ < R
    calc ‖shear k u c t w‖ = ‖(shear k u c t w - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖shear k u c t w - w‖ + ‖w‖ := norm_add_le _ _
      _ < R := by linarith [norm_nonneg w]
  have hcd : ∀ t ∈ strip s, DifferentiableAt ℂ c t := fun t ht =>
    hc.holo.differentiableAt ((sh_isOpen_strip s).mem_nhds ht)
  have hcd' : ∀ t ∈ strip s, DifferentiableAt ℂ (deriv c) t := fun t ht =>
    (sh_deriv_holo hc.holo).differentiableAt ((sh_isOpen_strip s).mem_nhds ht)
  refine ⟨r, hr0, by linarith, ?_, ?_, ?_⟩
  · -- the transformed Hamiltonian
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      have ht : q.2 ∈ strip s := hq.2
      have hsw : DifferentiableAt ℂ (fun q : C2 × ℂ => (q.2, q.1)) q :=
        differentiableAt_snd.prodMk differentiableAt_fst
      have hS : DifferentiableAt ℂ (fun q : C2 × ℂ => shear k u c q.2 q.1) q :=
        (shear_diffAt (k := k) (u := u) (q := (q.2, q.1)) (hcd q.2 ht)).comp
          (g := fun p : ℂ × C2 => shear k u c p.1 p.2) q hsw
      have hKd := hK.holo.differentiableAt
        (((sh_isOpen_polydisc R).prod (sh_isOpen_strip s)).mem_nhds
          (x := (shear k u c q.2 q.1, q.2)) ⟨hmaps q.2 ht q.1 hq.1, ht⟩)
      have h1 : DifferentiableAt ℂ (fun q : C2 × ℂ => K (shear k u c q.2 q.1) q.2) q :=
        hKd.comp (g := fun q : C2 × ℂ => K q.1 q.2) q (hS.prodMk differentiableAt_snd)
      have h2 : DifferentiableAt ℂ (fun q : C2 × ℂ => deriv c q.2) q :=
        (hcd' q.2 ht).comp q differentiableAt_snd
      have h3 : DifferentiableAt ℂ (fun q : C2 × ℂ => deriv c q.2 * lin u q.1 ^ k) q := by
        simp only [lin]; fun_prop
      exact (h1.sub h3).differentiableWithinAt
    · intro x t hx
      obtain ⟨y, hy⟩ := shear_real (k := k) (u := u) hc.real x t
      have hyR : ‖ofR y‖ < R := by
        rw [← hy]; exact hmaps t (sh_ofReal_mem_strip hs t) (ofR x) hx
      have hd := sh_real_of_im (sh_deriv_real hs hc.holo hc.real t)
      have hl : lin u (ofR x) = ((u 0 * x 0 + u 1 * x 1 : ℝ) : ℂ) := by simp [lin, ofR]
      simp only [shearK, hy, Complex.sub_im, hK.real y t hyR]
      rw [hd, hl, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
      simp
    · intro w t
      simp only [shearK, shear_per hc.per, sh_deriv_per hc.per, hK.per]
  · -- the conjugacy
    exact
      { holo := shear_holo hc.holo (polydisc r)
        maps := hmaps
        real := fun x t _ => shear_real hc.real x t
        per := shear_per hc.per
        zero := shear_zero (by omega) u c
        lin := shear_lin hk u c
        sol := fun γ a b hγ hmem => shear_sol hγ
          (fun t ht => sh_K_diffAt hK (sh_ofReal_mem_strip hs t)
            (hmaps t (sh_ofReal_mem_strip hs t) (γ t) (hmem t ht)))
          (fun t _ => hcd t (sh_ofReal_mem_strip hs t)) }
  · -- the estimate
    set A' := max A 0
    have hA' : 0 ≤ A' := le_max_right _ _
    refine ⟨16 * A' * D + |ν| * D ^ 2, fun w hw t ht => ?_⟩
    have hw' : ‖w‖ < r := hw
    have hw1 : ‖w‖ ≤ 1 := by linarith
    set v := shear k u c t w - w with hv
    have hv1 : ‖v‖ ≤ ‖w‖ / 2 := hsmall t ht w hw
    have hv2 : ‖v‖ ≤ D * ‖w‖ ^ (k - 1) := shear_sub_norm hu0 hu1 (hcB t ht).1 w
    have hSv : shear k u c t w = w + v := by rw [hv, add_sub_cancel]
    have hG : ‖(K (shear k u c t w) t - ν / 2 * q2 (shear k u c t w)) - (K w t - ν / 2 * q2 w)‖
        ≤ 16 * A' * ‖w‖ ^ 2 * ‖v‖ := by
      rw [hSv]
      by_cases hw0 : ‖w‖ = 0
      · have : v = 0 := norm_eq_zero.1 (le_antisymm (by linarith) (norm_nonneg _))
        simp [this, hw0]
      · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
        exact sh_schwarz (G := fun x => K x t - ν / 2 * q2 x) hA' (sh_G_holo hK ht ν)
          (fun x hx => (hb x hx t ht).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
          (by linarith) (by linarith)
    have hq : ‖(ν : ℂ) / 2 * q2 v‖ ≤ |ν| / 2 * (2 * ‖v‖ ^ 2) := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
      have := sh_norm_q2 v
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      gcongr
    have e1 : ‖w‖ ^ 2 * ‖w‖ ^ (k - 1) = ‖w‖ ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    have e2 : (‖w‖ ^ (k - 1)) ^ 2 = ‖w‖ ^ (2 * (k - 1)) := by
      rw [← pow_mul, mul_comm]
    have e3 : ‖w‖ ^ (2 * (k - 1)) ≤ ‖w‖ ^ (k + 1) :=
      pow_le_pow_of_le_one (norm_nonneg _) hw1 (by omega)
    have h4 : 16 * A' * ‖w‖ ^ 2 * ‖v‖ ≤ 16 * A' * D * ‖w‖ ^ (k + 1) := by
      calc 16 * A' * ‖w‖ ^ 2 * ‖v‖ ≤ 16 * A' * ‖w‖ ^ 2 * (D * ‖w‖ ^ (k - 1)) := by gcongr
        _ = 16 * A' * D * ‖w‖ ^ (k + 1) := by rw [← e1]; ring
    have h5 : |ν| / 2 * (2 * ‖v‖ ^ 2) ≤ |ν| * D ^ 2 * ‖w‖ ^ (k + 1) := by
      have : ‖v‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ (k + 1) := by
        calc ‖v‖ ^ 2 ≤ (D * ‖w‖ ^ (k - 1)) ^ 2 := by gcongr
          _ = D ^ 2 * ‖w‖ ^ (2 * (k - 1)) := by rw [mul_pow, e2]
          _ ≤ D ^ 2 * ‖w‖ ^ (k + 1) := by gcongr
      calc |ν| / 2 * (2 * ‖v‖ ^ 2) = |ν| * ‖v‖ ^ 2 := by ring
        _ ≤ |ν| * (D ^ 2 * ‖w‖ ^ (k + 1)) := by gcongr
        _ = |ν| * D ^ 2 * ‖w‖ ^ (k + 1) := by ring
    show ‖shearK k u c K w t - K w t - shX k u c ν w t‖ ≤ _
    rw [sh_identity]
    calc _ ≤ ‖(K (shear k u c t w) t - ν / 2 * q2 (shear k u c t w)) - (K w t - ν / 2 * q2 w)‖
          + ‖(ν : ℂ) / 2 * q2 v‖ := norm_add_le _ _
      _ ≤ 16 * A' * D * ‖w‖ ^ (k + 1) + |ν| * D ^ 2 * ‖w‖ ^ (k + 1) := by linarith
      _ = (16 * A' * D + |ν| * D ^ 2) * ‖w‖ ^ (k + 1) := by ring

theorem IsConj.comp {K₂ K₁ K : C2 → ℂ → ℂ} {Ψ₁ Ψ₂ : ℂ → C2 → C2} {r₂ r₁ R s : ℝ}
    (h₁ : IsConj K₁ K Ψ₁ r₁ R s) (h₂ : IsConj K₂ K₁ Ψ₂ r₂ r₁ s) (hs : 0 < s) :
    IsConj K₂ K (fun t w => Ψ₁ t (Ψ₂ t w)) r₂ R s where
  holo := by
    have hin : DifferentiableOn ℂ (fun q : ℂ × C2 => (q.1, Ψ₂ q.1 q.2)) (strip s ×ˢ polydisc r₂) :=
      differentiableOn_fst.prodMk h₂.holo
    refine h₁.holo.comp hin ?_
    intro q hq
    exact ⟨hq.1, h₂.maps q.1 hq.1 q.2 hq.2⟩
  maps t ht w hw := h₁.maps t ht _ (h₂.maps t ht w hw)
  real x t hx := by
    obtain ⟨y, hy⟩ := h₂.real x t hx
    have hm := h₂.maps t (sh_ofReal_mem_strip hs t) (ofR x) hx
    rw [hy] at hm
    obtain ⟨z, hz⟩ := h₁.real y t hm
    exact ⟨z, by simp only [hy, hz]⟩
  per t w := by simp only [h₁.per, h₂.per]
  zero t := by simp only [h₁.zero, h₂.zero]
  lin t := by
    have h1 := h₁.lin t
    rw [← h₂.zero t] at h1
    have := h1.comp 0 (h₂.lin t)
    simpa using this
  sol γ a b hγ hmem := by
    have hs2 := h₂.sol γ a b hγ hmem
    exact h₁.sol _ a b hs2 fun t ht =>
      h₂.maps t (sh_ofReal_mem_strip hs t) _ (hmem t ht)


end ABC.S4.R3Aux
