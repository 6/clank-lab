import ABC.S4.R2Aux7

/-! R2 helpers: the transformed Hamiltonian
`H₂(w,t) = ν/2 |w|² + H₁(Q(t)w, t) − ½ q_t(Q(t)w)`, `q_t(u) = Σ Aᵢⱼ uᵢ uⱼ`,
its holomorphy, realness, periodicity and the cubic remainder bound. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal Matrix

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

/-- What R2 needs of the Floquet matrix. -/
structure QData (H₁ : C2 → ℂ → ℂ) (s s₀ ν Kq : ℝ) (Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ) :
    Prop where
  s₀pos : 0 < s₀
  s₀le : s₀ ≤ s
  Kq0 : 0 ≤ Kq
  holo : ∀ i j, DifferentiableOn ℂ (fun t => Q t i j) (strip s₀)
  per : ∀ t, Q (t + 2 * π) = Q t
  det : ∀ t, (Q t).det = 1
  real : ∀ (t : ℝ) (i j : Fin 2), (Q t i j).im = 0
  bound : ∀ t : ℂ, |t.im| ≤ 3 * s₀ / 4 → ∀ i j, ‖Q t i j‖ ≤ Kq
  ode : ∀ t : ℂ, |t.im| < s₀ → ∀ i j,
    HasDerivAt (fun t => Q t i j) ((Bm H₁ t * Q t - (ν : ℂ) • (Q t * Jm)) i j) t

def qf (H₁ : C2 → ℂ → ℂ) (t : ℂ) (u : C2) : ℂ := ∑ i, ∑ j, Amat H₁ t i j * u i * u j

def remH (H₁ : C2 → ℂ → ℂ) (Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (w : C2) (t : ℂ) : ℂ :=
  H₁ (Q t *ᵥ w) t - qf H₁ t (Q t *ᵥ w) / 2

def H2 (H₁ : C2 → ℂ → ℂ) (Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ν : ℝ) (w : C2) (t : ℂ) : ℂ :=
  ν / 2 * (w 0 ^ 2 + w 1 ^ 2) + remH H₁ Q w t

theorem qf_smul (H₁ : C2 → ℂ → ℂ) (t z : ℂ) (u : C2) : qf H₁ t (z • u) = z ^ 2 * qf H₁ t u := by
  simp only [qf, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]; ring

theorem norm_mulVec_le {Q : Matrix (Fin 2) (Fin 2) ℂ} {K : ℝ} (hQ : ∀ i j, ‖Q i j‖ ≤ K)
    (w : C2) : ‖Q *ᵥ w‖ ≤ 2 * K * ‖w‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hQ 0 0)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc ‖Q i 0 * w 0 + Q i 1 * w 1‖ ≤ ‖Q i 0‖ * ‖w 0‖ + ‖Q i 1‖ * ‖w 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ K * ‖w‖ + K * ‖w‖ := by
        gcongr
        · exact hQ i 0
        · exact norm_le_pi_norm w 0
        · exact hQ i 1
        · exact norm_le_pi_norm w 1
    _ = 2 * K * ‖w‖ := by ring

theorem mulVec_real {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : ∀ i j, (Q i j).im = 0) {w : C2}
    (hw : ∀ i, (w i).im = 0) (i : Fin 2) : ((Q *ᵥ w) i).im = 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im, hQ, hw]

section H2

variable {H₁ : C2 → ℂ → ℂ} {ρ s s₀ ν Kq : ℝ} {Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ}

/-- The radius on which `Q(t) w` stays in `polydisc ρ`. -/
def rad (ρ Kq : ℝ) : ℝ := ρ / (4 * Kq + 2)

theorem rad_pos (hρ : 0 < ρ) (hK : 0 ≤ Kq) : 0 < rad ρ Kq := by unfold rad; positivity

theorem mulVec_mem (hρ : 0 < ρ) (hq : QData H₁ s s₀ ν Kq Q) {w : C2} (hw : ‖w‖ < 2 * rad ρ Kq)
    {t : ℂ} (ht : |t.im| ≤ 3 * s₀ / 4) : Q t *ᵥ w ∈ polydisc ρ := by
  have h := norm_mulVec_le (hq.bound t ht) w
  have hK := hq.Kq0
  show ‖Q t *ᵥ w‖ < ρ
  calc ‖Q t *ᵥ w‖ ≤ 2 * Kq * ‖w‖ := h
    _ ≤ 2 * Kq * (2 * rad ρ Kq) := by gcongr
    _ < ρ := by
        unfold rad
        rw [show 2 * Kq * (2 * (ρ / (4 * Kq + 2))) = ρ * (4 * Kq / (4 * Kq + 2)) by ring]
        have : 4 * Kq / (4 * Kq + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
        nlinarith

def Wset (ρ Kq s₀ : ℝ) : Set (C2 × ℂ) := polydisc (2 * rad ρ Kq) ×ˢ {t | |t.im| < 3 * s₀ / 4}

theorem isOpen_Wset (ρ Kq s₀ : ℝ) : IsOpen (Wset ρ Kq s₀) :=
  (isOpen_polydisc _).prod (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem mulVec_diff (hq : QData H₁ s s₀ ν Kq Q) :
    DifferentiableOn ℂ (fun q : C2 × ℂ => Q q.2 *ᵥ q.1) (Wset ρ Kq s₀) := by
  refine differentiableOn_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hQ : ∀ j, DifferentiableOn ℂ (fun q : C2 × ℂ => Q q.2 i j) (Wset ρ Kq s₀) := fun j =>
    (hq.holo i j).comp differentiableOn_snd fun q hq' => by
      have := hq'.2; simp only [mem_setOf_eq] at this
      show |q.2.im| < s₀; linarith [hq.s₀pos]
  have hw : ∀ j, DifferentiableOn ℂ (fun q : C2 × ℂ => q.1 j) (Wset ρ Kq s₀) := fun j =>
    (by fun_prop : Differentiable ℂ (fun q : C2 × ℂ => q.1 j)).differentiableOn
  exact ((hQ 0).mul (hw 0)).add ((hQ 1).mul (hw 1))

theorem remH_holo (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hq : QData H₁ s s₀ ν Kq Q) :
    DifferentiableOn ℂ (fun q : C2 × ℂ => remH H₁ Q q.1 q.2) (Wset ρ Kq s₀) := by
  have hstrip : ∀ q ∈ Wset ρ Kq s₀, q.2 ∈ strip s := fun q hq' => by
    have := hq'.2; simp only [mem_setOf_eq] at this
    show |q.2.im| < s; linarith [hq.s₀pos, hq.s₀le]
  have hmv := mulVec_diff (ρ := ρ) hq
  have h1 : DifferentiableOn ℂ (fun q : C2 × ℂ => H₁ (Q q.2 *ᵥ q.1) q.2) (Wset ρ Kq s₀) := by
    have := (Hh_holo hH).comp (hmv.prodMk differentiableOn_snd) fun q hq' =>
      mk_mem_prod (mulVec_mem hρ hq hq'.1 (le_of_lt hq'.2)) (hstrip q hq')
    exact this
  have hA : ∀ i j, DifferentiableOn ℂ (fun q : C2 × ℂ => Amat H₁ q.2 i j) (Wset ρ Kq s₀) :=
    fun i j => (Amat_holo hH hρ i j).comp differentiableOn_snd hstrip
  have hu : ∀ i, DifferentiableOn ℂ (fun q : C2 × ℂ => (Q q.2 *ᵥ q.1) i) (Wset ρ Kq s₀) :=
    fun i => differentiableOn_pi.1 hmv i
  have h2 : DifferentiableOn ℂ (fun q : C2 × ℂ => qf H₁ q.2 (Q q.2 *ᵥ q.1)) (Wset ρ Kq s₀) := by
    simp only [qf, Fin.sum_univ_two]
    exact (((hA 0 0).mul (hu 0)).mul (hu 0) |>.add (((hA 0 1).mul (hu 0)).mul (hu 1))).add
      ((((hA 1 0).mul (hu 1)).mul (hu 0)).add (((hA 1 1).mul (hu 1)).mul (hu 1)))
  refine h1.sub ((h2.mul_const ((2 : ℂ)⁻¹)).congr fun q _ => ?_)
  simp [div_eq_mul_inv]

theorem remH_per (hH : IsTPHam H₁ ρ s) (hq : QData H₁ s s₀ ν Kq Q) (w : C2) (t : ℂ) :
    remH H₁ Q w (t + 2 * π) = remH H₁ Q w t := by
  simp only [remH, qf, hq.per, hH.per, Amat_per hH]

theorem remH_real (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hs : 0 < s) (hq : QData H₁ s s₀ ν Kq Q)
    {x : E 2} (hx : ‖ofR x‖ < 2 * rad ρ Kq) (t : ℝ) : (remH H₁ Q (ofR x) t).im = 0 := by
  have hxr : ∀ i, (ofR x i).im = 0 := fun i => by simp [ofR]
  have hur := mulVec_real (hq.real t) hxr
  have hmem := mulVec_mem hρ hq hx (t := t) (by simp; positivity [hq.s₀pos])
  have h1 := real_pt hH hur hmem t
  set u := Q t *ᵥ ofR x with hu
  clear_value u
  have h2 : (qf H₁ t u).im = 0 := by
    simp [qf, Fin.sum_univ_two, Complex.mul_im, Complex.add_im, Amat_real hH hρ hs, hur]
  simp only [remH]
  rw [← hu, Complex.sub_im, h1, Complex.div_ofNat_im, h2]; simp

theorem remH_zero (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (t : ℂ) :
    remH H₁ Q 0 t = 0 := by
  simp [remH, qf, (h0 t).1]

/-- The cubic remainder bound. -/
theorem remH_bound (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hq : QData H₁ s s₀ ν Kq Q) :
    ∃ C, ∀ w ∈ polydisc (rad ρ Kq), ∀ t ∈ strip (s₀ / 2),
      ‖remH H₁ Q w t‖ ≤ C * ‖w‖ ^ 3 := by
  set ρ₁ := rad ρ Kq
  have hρ₁ : 0 < ρ₁ := rad_pos hρ hq.Kq0
  have hs₀ := hq.s₀pos
  -- a bound `M` on `closedBall 0 (3ρ₁/2) × {|Im t| ≤ s₀/2}`
  set Kt : Set ℂ := Icc 0 (2 * π) ×ℂ Icc (-(s₀ / 2)) (s₀ / 2)
  have hKc : IsCompact (closedBall (0 : C2) (3 * ρ₁ / 2) ×ˢ Kt) :=
    (isCompact_closedBall _ _).prod (isCompact_Icc.reProdIm isCompact_Icc)
  have hKW : closedBall (0 : C2) (3 * ρ₁ / 2) ×ˢ Kt ⊆ Wset ρ Kq s₀ := by
    rintro ⟨v, u⟩ ⟨hv, hu⟩
    simp only [Kt, Complex.mem_reProdIm, mem_Icc] at hu
    refine ⟨?_, ?_⟩
    · show ‖v‖ < 2 * ρ₁
      have := mem_closedBall_zero_iff.1 hv; linarith
    · show |u.im| < 3 * s₀ / 4
      exact abs_lt.2 ⟨by linarith, by linarith⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((remH_holo hH hρ hq).continuousOn.mono hKW)
  have hMb : ∀ v : C2, ‖v‖ ≤ 3 * ρ₁ / 2 → ∀ t : ℂ, |t.im| ≤ s₀ / 2 → ‖remH H₁ Q v t‖ ≤ M := by
    intro v hv t ht
    have hred : red t ∈ Kt := by
      have h := red_re t
      simp only [Kt, Complex.mem_reProdIm, mem_Icc, red_im]
      exact ⟨⟨h.1, h.2.le⟩, by linarith [(abs_le.1 ht).1], by linarith [(abs_le.1 ht).2]⟩
    have hper : Function.Periodic (remH H₁ Q v) (2 * π) := remH_per hH hq v
    have := hM (v, red t) ⟨mem_closedBall_zero_iff.2 hv, hred⟩
    simp only [red] at this
    rwa [hper.sub_int_mul_eq] at this
  refine ⟨M / ρ₁ ^ 3, fun w hw t ht => ?_⟩
  have hw' : ‖w‖ < ρ₁ := hw
  have ht' : |t.im| < s₀ / 2 := ht
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [remH_zero h0]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have htW : |t.im| < 3 * s₀ / 4 := by linarith
  have hts : t ∈ strip s := by show |t.im| < s; linarith [hq.s₀le]
  set u := Q t *ᵥ w
  set c := qf H₁ t u
  set G : C2 → ℂ := (H₁ · t)
  set f : ℂ → ℂ := fun z => remH H₁ Q (z • w) t
  have hf : f = fun z => G (z • u) - z ^ 2 * c / 2 := by
    funext z; simp only [f, remH, Matrix.mulVec_smul, qf_smul, G, u, c]
  set R := 3 * ρ₁ / 2 / ‖w‖
  have hR : 0 < R := by positivity
  have hzR : ∀ z : ℂ, ‖z‖ < R → ‖z • w‖ < 3 * ρ₁ / 2 := by
    intro z hz
    rw [norm_smul]
    calc ‖z‖ * ‖w‖ < R * ‖w‖ := by gcongr
      _ = 3 * ρ₁ / 2 := by simp only [R]; field_simp
  -- `G` is differentiable along `z • u` for small `z`
  have hGd : ∀ z : ℂ, ‖z‖ < R → DifferentiableAt ℂ G (z • u) := by
    intro z hz
    have hmem : (z • w, t) ∈ Wset ρ Kq s₀ := ⟨by show ‖z • w‖ < 2 * ρ₁; linarith [hzR z hz], htW⟩
    have := mulVec_mem hρ hq hmem.1 htW.le
    rw [Matrix.mulVec_smul] at this
    exact diffAt_slice hH (mk_mem_prod this hts)
  have hfd : DifferentiableOn ℂ f (ball 0 R) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [hf]
    exact (((hGd z hz).comp z ((differentiableAt_id).smul_const u)).sub
      (((differentiableAt_id.pow 2).mul_const c).div_const 2)).differentiableWithinAt
  have hfM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M := fun z hz =>
    hMb _ (hzR z (mem_ball_zero_iff.1 hz)).le t (by linarith)
  have hf0 : f 0 = 0 := by simp [f, remH_zero h0]
  -- derivatives at `0`
  set d : Fin 2 → C2 → ℂ := fun j v => fderiv ℂ G v (eC j)
  have hderiv : ∀ z : ℂ, ‖z‖ < R →
      HasDerivAt f (u 0 * d 0 (z • u) + u 1 * d 1 (z • u) - z * c) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => z • u) u z := by
      simpa using (hasDerivAt_id z).smul_const u
    have h2 := (hGd z hz).hasFDerivAt.comp_hasDerivAt z h1
    have h3 : HasDerivAt (fun z : ℂ => z ^ 2 * c / 2) (z * c) z := by
      have := ((hasDerivAt_pow 2 z).mul_const c).div_const 2
      convert this using 1; push_cast; ring
    rw [hf]
    refine (h2.sub h3).congr_deriv ?_
    have e := congrArg (fderiv ℂ G (z • u)) (eC_sum u)
    simp only [map_add, map_smul, smul_eq_mul] at e
    rw [e]
  have hR0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hf1 : deriv f 0 = 0 := by
    rw [(hderiv 0 (by simpa using hR)).deriv]
    simp [d, G, (h0 t).2]
  have hd : ∀ j, HasDerivAt (fun z : ℂ => d j (z • u))
      (u 0 * Amat H₁ t 0 j + u 1 * Amat H₁ t 1 j) 0 := by
    intro j
    obtain ⟨hd1, e1⟩ := hasFDerivAt_d1 hH hρ hts j
    have h1 : HasDerivAt (fun z : ℂ => z • u) u 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const u
    have hd1' : HasFDerivAt (d j) (fderiv ℂ (fun w => fderiv ℂ (H₁ · t) w (eC j)) 0)
        ((0 : ℂ) • u) := by simpa [d, G] using hd1
    have := hd1'.comp_hasDerivAt (0 : ℂ) h1
    rw [← e1]; exact this
  have hf2 : deriv (deriv f) 0 = 0 := by
    have hev : deriv f =ᶠ[𝓝 0] fun z => u 0 * d 0 (z • u) + u 1 * d 1 (z • u) - z * c := by
      filter_upwards [isOpen_ball.mem_nhds hR0] with z hz
      exact (hderiv z (mem_ball_zero_iff.1 hz)).deriv
    rw [hev.deriv_eq]
    have : HasDerivAt (fun z => u 0 * d 0 (z • u) + u 1 * d 1 (z • u) - z * c)
        (u 0 * (u 0 * Amat H₁ t 0 0 + u 1 * Amat H₁ t 1 0) +
          u 1 * (u 0 * Amat H₁ t 0 1 + u 1 * Amat H₁ t 1 1) - 1 * c) 0 :=
      (((hd 0).const_mul (u 0)).add ((hd 1).const_mul (u 1))).sub
        ((hasDerivAt_id' (0 : ℂ)).mul_const c)
    rw [this.deriv]
    simp only [c, qf, Fin.sum_univ_two]; ring
  -- the order-3 Schwarz bound at `z = 1`
  set r := ρ₁ / ‖w‖
  have hr1 : 1 ≤ r := by rw [le_div_iff₀ hwn]; linarith
  have hrR : r < R := by
    simp only [r, R]; rw [div_lt_div_iff_of_pos_right hwn]; linarith
  have := R2Aux.cubic_bound hfd hfM hf0 hf1 hf2 (by linarith) hrR
    (z := 1) (by simpa using hr1)
  simp only [f, one_smul, norm_one, one_pow, mul_one] at this
  calc ‖remH H₁ Q w t‖ ≤ M / r ^ 3 := this
    _ = M / ρ₁ ^ 3 * ‖w‖ ^ 3 := by simp only [r]; field_simp

end H2

end ABC.S4.R2Aux
