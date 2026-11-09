import ABC.S4.R1TranslateAux1

/-! R1 helpers: the complex inverse of `Φ` near a base point `b`, uniformly in `b`.
`psi M w b = b + (u, w₁)` with `u` the unique small root of `Φ(b + (u, w₁)) = Φ(b) + w`, for
`‖b‖ < M + 1` and `|sin b₁ + cos b₀| > 1/2`. -/

open Set Metric Filter Topology Real ComplexConjugate

noncomputable section

namespace ABC.S4.R1TranslateAux

/-- Componentwise conjugation. -/
def cconj (v : C2) : C2 := fun i => conj (v i)

lemma cconj_cconj (v : C2) : cconj (cconj v) = v := by
  ext i; simp [cconj]

lemma norm_cconj_le (v : C2) : ‖cconj v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => by
    simpa [cconj] using norm_le_pi_norm v i

lemma norm_cconj (v : C2) : ‖cconj v‖ = ‖v‖ :=
  le_antisymm (norm_cconj_le v) (by simpa [cconj_cconj] using norm_cconj_le (cconj v))

lemma norm_exp_le (w : ℂ) : ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (Complex.re_le_norm w)

lemma norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
  have h1 := norm_exp_le (z * Complex.I)
  have h2 := norm_exp_le (-z * Complex.I)
  simp only [norm_mul, Complex.norm_I, mul_one, norm_neg] at h1 h2
  rw [Complex.cos, norm_div, Complex.norm_two]
  have := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  linarith

lemma norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  have h1 := norm_exp_le (z * Complex.I)
  have h2 := norm_exp_le (-z * Complex.I)
  simp only [norm_mul, Complex.norm_I, mul_one, norm_neg] at h1 h2
  rw [Complex.sin, norm_div, Complex.norm_two, norm_mul, Complex.norm_I, mul_one]
  have := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  linarith

lemma sin_lip {R : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖Complex.sin x - Complex.sin y‖ ≤ Real.exp R * ‖x - y‖ :=
  (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_sin z).hasDerivWithinAt)
    (fun z hz => (norm_cos_le z).trans (Real.exp_le_exp.2 (mem_closedBall_zero_iff.1 hz)))
    (mem_closedBall_zero_iff.2 hy) (mem_closedBall_zero_iff.2 hx)

lemma cos_lip {R : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖Complex.cos x - Complex.cos y‖ ≤ Real.exp R * ‖x - y‖ :=
  (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_cos z).hasDerivWithinAt)
    (fun z hz => by
      rw [norm_neg]
      exact (norm_sin_le z).trans (Real.exp_le_exp.2 (mem_closedBall_zero_iff.1 hz)))
    (mem_closedBall_zero_iff.2 hy) (mem_closedBall_zero_iff.2 hx)

/-- The constants: a Lipschitz bound for `sin`, `cos` on the `M + 2` disc, and two radii. -/
def Lc (M : ℝ) : ℝ := Real.exp (M + 2)

def r2 (M : ℝ) : ℝ := 1 / (8 * Lc M)

def r1 (M : ℝ) : ℝ := r2 M / (8 * ((M + 1) * Lc M + 1))

lemma Lc_pos (M : ℝ) : 0 < Lc M := Real.exp_pos _

lemma one_le_Lc {M : ℝ} (hM : 0 ≤ M) : 1 ≤ Lc M := Real.one_le_exp (by linarith)

lemma r2_pos (M : ℝ) : 0 < r2 M := by unfold r2; have := Lc_pos M; positivity

lemma r1_pos {M : ℝ} (hM : 0 ≤ M) : 0 < r1 M := by
  unfold r1; have := r2_pos M; have := Lc_pos M; positivity

lemma r2_le {M : ℝ} (hM : 0 ≤ M) : r2 M ≤ 1 / 8 := by
  unfold r2
  rw [div_le_div_iff₀ (by have := Lc_pos M; positivity) (by norm_num)]
  have := one_le_Lc hM; linarith

lemma r1_le {M : ℝ} (hM : 0 ≤ M) : r1 M ≤ r2 M / 8 := by
  unfold r1
  have h2 := r2_pos M
  have hL := Lc_pos M
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 1 ≤ (M + 1) * Lc M + 1 := by nlinarith
  nlinarith

/-- The parameter domain `(w, b)`. -/
def Dset (M : ℝ) : Set (C2 × C2) :=
  {x | ‖x.1‖ < r1 M ∧ ‖x.2‖ < M + 1 ∧
    1 / 2 < ‖Complex.sin (x.2 1) + Complex.cos (x.2 0)‖}

lemma isOpen_Dset (M : ℝ) : IsOpen (Dset M) := by
  have hc : Continuous fun x : C2 × C2 => Complex.sin (x.2 1) + Complex.cos (x.2 0) :=
    (Complex.continuous_sin.comp ((continuous_apply 1).comp continuous_snd)).add
      (Complex.continuous_cos.comp ((continuous_apply 0).comp continuous_snd))
  exact (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).inter
      (isOpen_lt continuous_const hc.norm))

/-- `Φ₀(b + (u, w₁)) - Φ₀(b) - w₀`. -/
def fimp (x : ℂ × (C2 × C2)) : ℂ :=
  (x.2.2 0 + x.1) * Complex.sin (x.2.2 1 + x.2.1 1) + Complex.sin (x.2.2 0 + x.1)
    - (x.2.2 0 * Complex.sin (x.2.2 1) + Complex.sin (x.2.2 0)) - x.2.1 0

lemma contDiff_fimp {n : WithTop ℕ∞} : ContDiff ℂ n fimp := by
  have h0 : ∀ i : Fin 2, ContDiff ℂ n fun x : ℂ × (C2 × C2) => x.2.2 i := fun i =>
    (contDiff_apply ℂ ℂ i).comp (contDiff_snd.comp contDiff_snd)
  have hw : ∀ i : Fin 2, ContDiff ℂ n fun x : ℂ × (C2 × C2) => x.2.1 i := fun i =>
    (contDiff_apply ℂ ℂ i).comp (contDiff_fst.comp contDiff_snd)
  unfold fimp
  exact (((((h0 0).add contDiff_fst).mul (Complex.contDiff_sin.comp ((h0 1).add (hw 1)))).add
    (Complex.contDiff_sin.comp ((h0 0).add contDiff_fst))).sub
    (((h0 0).mul (Complex.contDiff_sin.comp (h0 1))).add (Complex.contDiff_sin.comp (h0 0)))).sub
    (hw 0)

lemma hasDerivAt_fimp (u : ℂ) (w b : C2) :
    HasDerivAt (fun u => fimp (u, (w, b)))
      (Complex.sin (b 1 + w 1) + Complex.cos (b 0 + u)) u := by
  have h1 : HasDerivAt (fun u : ℂ => (b 0 + u) * Complex.sin (b 1 + w 1))
      (Complex.sin (b 1 + w 1)) u := by
    simpa using ((hasDerivAt_id' u).const_add (b 0)).mul_const (Complex.sin (b 1 + w 1))
  have h2 : HasDerivAt (fun u : ℂ => Complex.sin (b 0 + u)) (Complex.cos (b 0 + u)) u := by
    simpa [Function.comp_def] using
      (Complex.hasDerivAt_sin (b 0 + u)).comp u ((hasDerivAt_id' u).const_add (b 0))
  have := ((h1.add h2).sub_const (b 0 * Complex.sin (b 1) + Complex.sin (b 0))).sub_const (w 0)
  simpa [fimp] using this

section consts

variable {M : ℝ} (hM : 0 ≤ M)
include hM

/-- The `u`-derivative stays within `1/4` of `sin b₁ + cos b₀`. -/
lemma fimp_deriv_near {w b : C2} (hx : (w, b) ∈ Dset M) {u : ℂ} (hu : u ∈ ball (0 : ℂ) (r2 M)) :
    ‖(Complex.sin (b 1 + w 1) + Complex.cos (b 0 + u)) -
      (Complex.sin (b 1) + Complex.cos (b 0))‖ ≤ 1 / 4 := by
  obtain ⟨hw, hb, -⟩ := hx
  simp only at hw hb
  have hu' : ‖u‖ < r2 M := mem_ball_zero_iff.1 hu
  have h2 := r2_le hM
  have h1 := r1_le hM
  have hr2 := r2_pos M
  have hb0 : ‖b 0‖ ≤ M + 1 := (norm_le_pi_norm b 0).trans hb.le
  have hb1 : ‖b 1‖ ≤ M + 1 := (norm_le_pi_norm b 1).trans hb.le
  have hw1 : ‖w 1‖ ≤ r1 M := (norm_le_pi_norm w 1).trans hw.le
  have hs := sin_lip (R := M + 2) (x := b 1 + w 1) (y := b 1)
    ((norm_add_le _ _).trans (by linarith)) (by linarith)
  have hc := cos_lip (R := M + 2) (x := b 0 + u) (y := b 0)
    ((norm_add_le _ _).trans (by linarith)) (by linarith)
  simp only [add_sub_cancel_left] at hs hc
  have hL : Lc M * r2 M = 1 / 8 := by have := (Lc_pos M).ne'; unfold r2; field_simp
  calc _ = ‖(Complex.sin (b 1 + w 1) - Complex.sin (b 1)) +
        (Complex.cos (b 0 + u) - Complex.cos (b 0))‖ := by ring_nf
    _ ≤ Lc M * ‖w 1‖ + Lc M * ‖u‖ := (norm_add_le _ _).trans (add_le_add hs hc)
    _ ≤ Lc M * r2 M + Lc M * r2 M := by
        have := Lc_pos M
        gcongr
        · linarith
    _ = 1 / 4 := by rw [hL]; norm_num

lemma fimp_zero_small {w b : C2} (hx : (w, b) ∈ Dset M) :
    ‖fimp (0, (w, b))‖ ≤ r2 M / 8 := by
  obtain ⟨hw, hb, -⟩ := hx
  simp only at hw hb
  have hb0 : ‖b 0‖ ≤ M + 1 := (norm_le_pi_norm b 0).trans hb.le
  have hb1 : ‖b 1‖ ≤ M + 1 := (norm_le_pi_norm b 1).trans hb.le
  have hw0 : ‖w 0‖ ≤ r1 M := (norm_le_pi_norm w 0).trans hw.le
  have hw1 : ‖w 1‖ ≤ r1 M := (norm_le_pi_norm w 1).trans hw.le
  have h1 := r1_le hM
  have h2 := r2_le hM
  have hs := sin_lip (R := M + 2) (x := b 1 + w 1) (y := b 1)
    ((norm_add_le _ _).trans (by linarith)) (by linarith)
  simp only [add_sub_cancel_left] at hs
  have e : fimp (0, (w, b)) = b 0 * (Complex.sin (b 1 + w 1) - Complex.sin (b 1)) - w 0 := by
    simp [fimp]; ring
  have hL := Lc_pos M
  have hr1 : ((M + 1) * Lc M + 1) * r1 M = r2 M / 8 := by
    unfold r1; field_simp
  rw [e]
  calc _ ≤ ‖b 0‖ * ‖Complex.sin (b 1 + w 1) - Complex.sin (b 1)‖ + ‖w 0‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ (M + 1) * (Lc M * r1 M) + r1 M := by
        gcongr
        · exact hs.trans (by unfold Lc; gcongr)
    _ = r2 M / 8 := by rw [← hr1]; ring

lemma fimp_root {w b : C2} (hx : (w, b) ∈ Dset M) :
    (∃ u ∈ ball (0 : ℂ) (r2 M), fimp (u, (w, b)) = 0) ∧
      ∀ u ∈ ball (0 : ℂ) (r2 M), ∀ v ∈ ball (0 : ℂ) (r2 M),
        fimp (u, (w, b)) = 0 → fimp (v, (w, b)) = 0 → u = v := by
  have ha : 1 / 2 < ‖Complex.sin (b 1) + Complex.cos (b 0)‖ := hx.2.2
  have ha0 : Complex.sin (b 1) + Complex.cos (b 0) ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; norm_num at ha
  have hr := root_of_deriv_near (g := fun u => fimp (u, (w, b))) (r := r2 M) ha0
    (fun u _ => (hasDerivAt_fimp u w b).differentiableAt)
    (fun u hu => by
      rw [(hasDerivAt_fimp u w b).deriv]
      exact (fimp_deriv_near hM hx hu).trans (by linarith))
    (by
      have := fimp_zero_small hM hx
      have := r2_pos M
      nlinarith)
  refine ⟨hr.1, fun u hu v hv h1 h2 => ?_⟩
  have := hr.2 u hu v hv
  simp only [h1, h2, sub_self, norm_zero] at this
  have hp : 0 < ‖Complex.sin (b 1) + Complex.cos (b 0)‖ / 2 := by linarith
  have : ‖u - v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (u - v)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end consts

open Classical in
/-- The small root `u`. -/
def Ufn (M : ℝ) (w b : C2) : ℂ :=
  if h : ∃ u ∈ ball (0 : ℂ) (r2 M), fimp (u, (w, b)) = 0 then h.choose else 0

/-- `Φ⁻¹(Φ(b) + w)` near `b`. -/
def psi (M : ℝ) (w b : C2) : C2 := ![b 0 + Ufn M w b, b 1 + w 1]

section consts2

variable {M : ℝ} (hM : 0 ≤ M)
include hM

lemma Ufn_spec {w b : C2} (hx : (w, b) ∈ Dset M) :
    Ufn M w b ∈ ball (0 : ℂ) (r2 M) ∧ fimp (Ufn M w b, (w, b)) = 0 := by
  have h := (fimp_root hM hx).1
  unfold Ufn; rw [dif_pos h]; exact h.choose_spec

lemma Ufn_unique {w b : C2} (hx : (w, b) ∈ Dset M) {u : ℂ} (hu : u ∈ ball (0 : ℂ) (r2 M))
    (h : fimp (u, (w, b)) = 0) : u = Ufn M w b :=
  (fimp_root hM hx).2 u hu _ (Ufn_spec hM hx).1 h (Ufn_spec hM hx).2

lemma Ufn_holo : DifferentiableOn ℂ (fun x : C2 × C2 => Ufn M x.1 x.2) (Dset M) := by
  refine implicit_holo (f := fimp) contDiff_fimp (isOpen_Dset M) (r := r2 M)
    (fun x hx => Ufn_spec hM hx) (fun x hx u hu h => Ufn_unique hM hx hu h) ?_
  intro x hx
  have hd : fderiv ℂ fimp (Ufn M x.1 x.2, x) (1, 0) =
      Complex.sin (x.2 1 + x.1 1) + Complex.cos (x.2 0 + Ufn M x.1 x.2) := by
    have h1 : HasDerivAt (fun u : ℂ => ((u, x) : ℂ × (C2 × C2))) ((1 : ℂ), (0 : C2 × C2))
        (Ufn M x.1 x.2) := (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    have h2 := ((contDiff_fimp (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt
      _ h1
    exact h2.unique (hasDerivAt_fimp _ x.1 x.2)
  rw [hd]
  intro h0
  have := fimp_deriv_near hM hx (Ufn_spec hM hx).1
  rw [h0, zero_sub, norm_neg] at this
  have := hx.2.2
  linarith

lemma Ufn_zero {b : C2} (hx : ((0 : C2), b) ∈ Dset M) : Ufn M 0 b = 0 :=
  (Ufn_unique hM hx (mem_ball_self (r2_pos M)) (by simp [fimp])).symm

lemma Dset_cconj {w b : C2} (hx : (w, b) ∈ Dset M) : (cconj w, cconj b) ∈ Dset M := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨by simpa [norm_cconj] using h1, by simpa [norm_cconj] using h2, ?_⟩
  simp only [cconj]
  rw [Complex.sin_conj, Complex.cos_conj, ← map_add, Complex.norm_conj]
  exact h3

omit hM in
lemma fimp_conj (u : ℂ) (w b : C2) :
    fimp (conj u, (cconj w, cconj b)) = conj (fimp (u, (w, b))) := by
  simp [fimp, cconj, ← Complex.sin_conj]

lemma Ufn_cconj {w b : C2} (hx : (w, b) ∈ Dset M) :
    Ufn M (cconj w) (cconj b) = conj (Ufn M w b) := by
  have hs := Ufn_spec hM hx
  refine (Ufn_unique hM (Dset_cconj hM hx) ?_ ?_).symm
  · rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hs.1
  · rw [fimp_conj, hs.2, map_zero]

lemma psi_cconj {w b : C2} (hx : (w, b) ∈ Dset M) :
    psi M (cconj w) (cconj b) = cconj (psi M w b) := by
  ext i; fin_cases i <;> simp [psi, cconj, Ufn_cconj hM hx]

lemma psi_zero {b : C2} (hx : ((0 : C2), b) ∈ Dset M) : psi M 0 b = b := by
  ext i; fin_cases i <;> simp [psi, Ufn_zero hM hx]

lemma phiC_psi {w b : C2} (hx : (w, b) ∈ Dset M) : phiC (psi M w b) = phiC b + w := by
  have h := (Ufn_spec hM hx).2
  simp only [fimp] at h
  ext i; fin_cases i
  · simp [phiC, psi]; linear_combination h
  · simp [phiC, psi]

lemma psi_unique {w b q : C2} (hx : (w, b) ∈ Dset M) (h1 : q 1 = b 1 + w 1)
    (h0 : ‖q 0 - b 0‖ < r2 M) (hq : phiC q = phiC b + w) : psi M w b = q := by
  have hr : fimp (q 0 - b 0, (w, b)) = 0 := by
    have := congrFun hq 0
    simp [phiC] at this
    simp only [fimp, add_sub_cancel, ← h1]
    linear_combination this
  have := Ufn_unique hM hx (mem_ball_zero_iff.2 h0) hr
  ext i; fin_cases i
  · simp [psi, ← this]
  · simp [psi, h1]

lemma psi_rho {w b : C2} (hx : (w, b) ∈ Dset M) :
    1 / 4 ≤ ‖Complex.sin (psi M w b 1) + Complex.cos (psi M w b 0)‖ := by
  have h := fimp_deriv_near hM hx (Ufn_spec hM hx).1
  have h3 := hx.2.2
  simp only [psi, Matrix.cons_val_one, Matrix.cons_val_zero]
  have := norm_sub_norm_le (Complex.sin (b 1) + Complex.cos (b 0))
    (Complex.sin (b 1 + w 1) + Complex.cos (b 0 + Ufn M w b))
  rw [norm_sub_rev] at this
  linarith

end consts2

end ABC.S4.R1TranslateAux
