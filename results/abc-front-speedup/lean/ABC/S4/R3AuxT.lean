import ABC.S4.R3AuxP

/-! R3 auxiliaries: Taylor coefficients to order 4 by Cauchy integrals, and their uniqueness. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real MeasureTheory

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

theorem norm_twoPiI_inv_mul_circleIntegral_le {g : ℂ → ℂ} {r K : ℝ} (hr : 0 ≤ r)
    (hg : ∀ ζ ∈ sphere (0 : ℂ) r, ‖g ζ‖ ≤ K) :
    ‖(2 * π * Complex.I)⁻¹ * ∮ ζ in C(0, r), g ζ‖ ≤ r * K := by
  have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hg
  simpa [smul_eq_mul] using this

theorem norm_cI_le {f : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) (hf : ContinuousOn f (sphere 0 r))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) r, ‖f ζ‖ ≤ M) (n : ℕ) : ‖cI r f n‖ ≤ M / r ^ n := by
  have h := norm_twoPiI_inv_mul_circleIntegral_le (g := fun ζ => (ζ ^ (n + 1))⁻¹ * f ζ)
    (K := M / r ^ (n + 1)) hr.le (by
      intro ζ hζ
      have hζr : ‖ζ‖ = r := by simpa using hζ
      rw [norm_mul, norm_inv, norm_pow, hζr, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hM ζ hζ) (by positivity))
  unfold cI
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- the geometric-series identity behind the Cauchy-Taylor expansion -/
theorem cauchy_kernel_step {ζ z : ℂ} (hζ : ζ ≠ 0) (hζz : ζ - z ≠ 0) (N : ℕ) :
    (z / ζ) ^ N * (ζ - z)⁻¹ - z ^ N * (ζ ^ (N + 1))⁻¹ = (z / ζ) ^ (N + 1) * (ζ - z)⁻¹ := by
  rw [div_pow, div_pow]
  field_simp
  ring

theorem taylor_circle {f : ℂ → ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ ζ ∈ sphere (0 : ℂ) r, ‖f ζ‖ ≤ M) (N : ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ r / 2) :
    ‖f z - ∑ n ∈ Finset.range N, cI r f n * z ^ n‖ ≤ 2 * M * (‖z‖ / r) ^ N := by
  have hsph : sphere (0 : ℂ) r ⊆ ball 0 R := fun ζ hζ => by
    simp only [mem_sphere_iff_norm, sub_zero] at hζ; simpa [hζ] using hrR
  have hfc : ContinuousOn f (sphere 0 r) := hf.continuousOn.mono hsph
  have hne0 : ∀ ζ ∈ sphere (0 : ℂ) r, ζ ≠ 0 := fun ζ hζ h0 => by
    subst h0; simp at hζ; linarith
  have hnez : ∀ ζ ∈ sphere (0 : ℂ) r, ζ - z ≠ 0 := fun ζ hζ h0 => by
    have : ζ = z := sub_eq_zero.mp h0
    subst this; simp at hζ; linarith
  -- remainder integrand
  set Rm : ℕ → ℂ → ℂ := fun k ζ => (z / ζ) ^ k * (ζ - z)⁻¹ * f ζ with hRm
  have hRmi : ∀ k, CircleIntegrable (Rm k) 0 r := fun k => by
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) hfc
    · exact ((continuousOn_const.div continuousOn_id hne0)).pow k
    · exact (continuousOn_id.sub continuousOn_const).inv₀ hnez
  have hci : ∀ k, CircleIntegrable (fun ζ => z ^ k * ((ζ ^ (k + 1))⁻¹ * f ζ)) 0 r := fun k => by
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine continuousOn_const.mul (ContinuousOn.mul ?_ hfc)
    exact (continuousOn_id.pow _).inv₀ fun ζ hζ => pow_ne_zero _ (hne0 ζ hζ)
  have key : ∀ k, f z - ∑ n ∈ Finset.range k, cI r f n * z ^ n =
      (2 * π * Complex.I)⁻¹ * ∮ ζ in C(0, r), Rm k ζ := by
    intro k
    induction k with
    | zero =>
      have hdc : DiffContOnCl ℂ f (ball 0 r) :=
        hf.diffContOnCl_ball (closedBall_subset_ball hrR)
      have hzb : z ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff]; linarith
      have := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzb
      simp only [smul_eq_mul] at this
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, hRm, pow_zero, one_mul]
      exact this.symm
    | succ k ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih]
      have : ∮ ζ in C(0, r), Rm (k + 1) ζ =
          (∮ ζ in C(0, r), Rm k ζ) - ∮ ζ in C(0, r), z ^ k * ((ζ ^ (k + 1))⁻¹ * f ζ) := by
        rw [← circleIntegral.integral_sub (hRmi k) (hci k)]
        refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
        simp only [hRm]
        rw [← cauchy_kernel_step (hne0 ζ hζ) (hnez ζ hζ) k]
        ring
      rw [this, circleIntegral.integral_const_mul]
      unfold cI
      ring
  rw [key N]
  have hb := norm_twoPiI_inv_mul_circleIntegral_le (g := Rm N)
    (K := (‖z‖ / r) ^ N * (2 / r) * M) hr.le (by
      intro ζ hζ
      have hζr : ‖ζ‖ = r := by simpa using hζ
      have hd : r / 2 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le ζ z
        linarith
      simp only [hRm]
      rw [norm_mul, norm_mul, norm_pow, norm_div, hζr, norm_inv]
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ζ hζ)
      gcongr
      · rw [inv_le_comm₀ (by linarith) (by positivity)]
        rw [inv_div]; exact hd
      · exact hM ζ hζ)
  refine hb.trans (le_of_eq ?_)
  field_simp

/-- a one-variable polynomial that is `O(x^j)` as `x → 0⁺` has no terms of degree `< j` -/
theorem poly1_vanish : ∀ (j N : ℕ) (c : ℕ → ℂ) {r C : ℝ}, 0 < r →
    (∀ x : ℝ, 0 < x → x < r → ‖∑ k ∈ Finset.range N, c k * (x : ℂ) ^ k‖ ≤ C * x ^ j) →
    ∀ k, k < j → k < N → c k = 0 := by
  intro j
  induction j with
  | zero => intro N c r C _ _ k hk; omega
  | succ j ih =>
    intro N c r C hr h k hkj hkN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hc0 : c 0 = 0 := by
      have hcont : Continuous (fun x : ℝ => ∑ k ∈ Finset.range (N' + 1), c k * (x : ℂ) ^ k) := by
        fun_prop
      have h0 : (∑ k ∈ Finset.range (N' + 1), c k * ((0 : ℝ) : ℂ) ^ k) = c 0 := by
        rw [Finset.sum_range_succ']; simp
      have t1 : Tendsto (fun x : ℝ => ‖∑ k ∈ Finset.range (N' + 1), c k * (x : ℂ) ^ k‖)
          (𝓝[>] 0) (𝓝 ‖c 0‖) := by
        rw [← h0]; exact ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).norm
      have t2 : Tendsto (fun x : ℝ => C * x ^ (j + 1)) (𝓝[>] 0) (𝓝 0) := by
        have : Continuous (fun x : ℝ => C * x ^ (j + 1)) := by fun_prop
        have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      have ev : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ),
          ‖∑ k ∈ Finset.range (N' + 1), c k * (x : ℂ) ^ k‖ ≤ C * x ^ (j + 1) := by
        filter_upwards [Ioo_mem_nhdsGT hr] with x hx using h x hx.1 hx.2
      exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto t1 t2 ev)
    have h' : ∀ x : ℝ, 0 < x → x < r →
        ‖∑ k ∈ Finset.range N', c (k + 1) * (x : ℂ) ^ k‖ ≤ C * x ^ j := by
      intro x hx hxr
      have e : (∑ k ∈ Finset.range (N' + 1), c k * (x : ℂ) ^ k) =
          (x : ℂ) * ∑ k ∈ Finset.range N', c (k + 1) * (x : ℂ) ^ k := by
        rw [Finset.sum_range_succ', hc0, Finset.mul_sum]
        simp only [pow_zero, mul_one, add_zero]
        refine Finset.sum_congr rfl fun k _ => by ring
      have := h x hx hxr
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, pow_succ] at this
      have : x * ‖∑ k ∈ Finset.range N', c (k + 1) * (x : ℂ) ^ k‖ ≤ x * (C * x ^ j) := by
        linarith
      exact le_of_mul_le_mul_left this hx
    rcases k with _ | k
    · exact hc0
    · exact ih N' (fun k => c (k + 1)) hr h' k (by omega) (by omega)

theorem poly4_line (a : ℕ → ℕ → ℂ) (x b : ℂ) :
    poly4 a ![x, x * b] =
      ∑ k ∈ Finset.range 5, (∑ n ∈ Finset.range (k + 1), a (k - n) n * b ^ n) * x ^ k := by
  simp [poly4, Finset.sum_range_succ]
  ring

/-- a polynomial of degree `≤ 4` that is `O(|x|^j)` at real points has no terms of degree `< j` -/
theorem poly4_vanish {a : ℕ → ℕ → ℂ} {r C : ℝ} {j : ℕ} (hr : 0 < r)
    (h : ∀ x y : ℝ, |x| < r → |y| < r → ‖poly4 a ![(x : ℂ), (y : ℂ)]‖ ≤ C * max |x| |y| ^ j) :
    ∀ m n, m + n < j → m + n ≤ 4 → a m n = 0 := by
  have hk : ∀ b : ℝ, ∀ k, k < j → k < 5 →
      ∑ n ∈ Finset.range (k + 1), a (k - n) n * (b : ℂ) ^ n = 0 := by
    intro b
    have hK : 0 < max 1 |b| := lt_max_of_lt_left one_pos
    refine poly1_vanish j 5 (fun k => ∑ n ∈ Finset.range (k + 1), a (k - n) n * (b : ℂ) ^ n)
      (r := r / max 1 |b|) (C := max C 0 * max 1 |b| ^ j) (by positivity) ?_
    intro x hx hxr
    rw [lt_div_iff₀ hK] at hxr
    rw [← poly4_line]
    have hx1 : |x| < r := by
      rw [abs_of_pos hx]; nlinarith [le_max_left 1 |b|]
    have hx2 : |x * b| < r := by
      rw [abs_mul, abs_of_pos hx]; nlinarith [le_max_right 1 |b|]
    have := h x (x * b) hx1 hx2
    push_cast at this
    refine this.trans ?_
    have hm : max |x| |x * b| ≤ x * max 1 |b| := by
      rw [abs_mul, abs_of_pos hx, mul_max_of_nonneg _ _ hx.le, mul_one]
    calc C * max |x| |x * b| ^ j ≤ max C 0 * max |x| |x * b| ^ j := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (x * max 1 |b|) ^ j := by
          gcongr
      _ = max C 0 * max 1 |b| ^ j * x ^ j := by ring
  intro m n hj h4
  have := poly1_vanish (m + n + 1) (m + n + 1) (fun n' => a (m + n - n') n') (r := 1) (C := 0)
    one_pos (fun x _ _ => by
      rw [hk x (m + n) hj (by omega)]; simp) n (by omega) (by omega)
  simpa using this

/-! ### Extraction of the Taylor coefficients -/

theorem isOpen_strip' (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem sphere_subset_ball' {r R : ℝ} (hrR : r < R) : sphere (0 : ℂ) r ⊆ ball 0 R := fun ζ hζ => by
  rw [mem_sphere_zero_iff_norm] at hζ; rw [mem_ball_zero_iff, hζ]; exact hrR

theorem ne_zero_of_mem_sphere' {r : ℝ} (hr : 0 < r) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) r) :
    ζ ≠ 0 := by
  rintro rfl; simp at hζ; linarith

theorem vec2_norm_lt {R : ℝ} {a b : ℂ} (ha : ‖a‖ < R) (hb : ‖b‖ < R) :
    ‖(![a, b] : C2)‖ < R := by
  have hR : 0 < R := (norm_nonneg a).trans_lt ha
  rw [pi_norm_lt_iff hR]
  intro i; fin_cases i <;> simpa

theorem vec2_eta (w : C2) : (![w 0, w 1] : C2) = w := by
  funext i; fin_cases i <;> rfl

theorem G_comp_contOn {G : C2 → ℂ → ℂ} {R s : ℝ} (hG : IsTPHam G R s) {X : Type*}
    [TopologicalSpace X] {S : Set X} {φ ψ τ : X → ℂ} (hφ : ContinuousOn φ S)
    (hψ : ContinuousOn ψ S) (hτ : ContinuousOn τ S)
    (hmap : ∀ x ∈ S, ‖φ x‖ < R ∧ ‖ψ x‖ < R ∧ τ x ∈ strip s) :
    ContinuousOn (fun x => G ![φ x, ψ x] (τ x)) S := by
  have h1 : ContinuousOn (fun x => ((![φ x, ψ x] : C2), τ x)) S := by
    refine ContinuousOn.prodMk ?_ hτ
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i <;> simpa
  exact hG.holo.continuousOn.comp h1 fun x hx =>
    ⟨vec2_norm_lt (hmap x hx).1 (hmap x hx).2.1, (hmap x hx).2.2⟩

theorem G_comp_diffOn {G : C2 → ℂ → ℂ} {R s : ℝ} (hG : IsTPHam G R s) {S : Set ℂ}
    {φ ψ τ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ S)
    (hψ : DifferentiableOn ℂ ψ S) (hτ : DifferentiableOn ℂ τ S)
    (hmap : ∀ x ∈ S, ‖φ x‖ < R ∧ ‖ψ x‖ < R ∧ τ x ∈ strip s) :
    DifferentiableOn ℂ (fun x => G ![φ x, ψ x] (τ x)) S := by
  have h1 : DifferentiableOn ℂ (fun x => ((![φ x, ψ x] : C2), τ x)) S := by
    refine DifferentiableOn.prodMk ?_ hτ
    refine differentiableOn_pi.2 fun i => ?_
    fin_cases i <;> simpa
  exact hG.holo.comp h1 fun x hx =>
    ⟨vec2_norm_lt (hmap x hx).1 (hmap x hx).2.1, (hmap x hx).2.2⟩

/-- first Cauchy coefficient, in `w₀` -/
def eA (G : C2 → ℂ → ℂ) (r : ℝ) (m : ℕ) (w1 t : ℂ) : ℂ := cI r (fun ζ => G ![ζ, w1] t) m

/-- second Cauchy coefficient, in `w₁` -/
def eB (G : C2 → ℂ → ℂ) (r : ℝ) (m n : ℕ) (t : ℂ) : ℂ := cI r (fun w1 => eA G r m w1 t) n

/-- the coefficients, truncated to degree `≤ 4` -/
def eC (G : C2 → ℂ → ℂ) (r : ℝ) (m n : ℕ) (t : ℂ) : ℂ := if m + n ≤ 4 then eB G r m n t else 0

section
variable {G : C2 → ℂ → ℂ} {R s r M : ℝ}

theorem eA_contOn (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R) (m : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => eA G r m p.1 p.2) (ball 0 R ×ˢ strip s) := by
  unfold eA cI
  refine continuousOn_const.mul ?_
  refine continuousOn_circleIntegral_param (φ := fun ζ p => (ζ ^ (m + 1))⁻¹ * G ![ζ, p.1] p.2)
    hr ?_
  refine ContinuousOn.mul ?_ ?_
  · exact (continuousOn_fst.pow _).inv₀ fun p hp =>
      pow_ne_zero _ (ne_zero_of_mem_sphere' hr hp.1)
  · refine G_comp_contOn hG continuousOn_fst (continuous_fst.comp continuous_snd).continuousOn
      (continuous_snd.comp continuous_snd).continuousOn fun p hp => ⟨?_, ?_, hp.2.2⟩
    · exact mem_ball_zero_iff.mp (sphere_subset_ball' hrR hp.1)
    · exact mem_ball_zero_iff.mp hp.2.1

theorem eA_diff_w1 (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R) (m : ℕ) {t : ℂ}
    (ht : t ∈ strip s) : DifferentiableOn ℂ (fun w1 => eA G r m w1 t) (ball 0 R) := by
  unfold eA cI
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_circleIntegral_of_holo (φ := fun ζ w1 => (ζ ^ (m + 1))⁻¹ * G ![ζ, w1] t)
    isOpen_ball hr ?_ ?_
  · refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_fst.pow _).inv₀ fun p hp =>
        pow_ne_zero _ (ne_zero_of_mem_sphere' hr hp.1)
    · refine G_comp_contOn hG continuousOn_fst continuousOn_snd continuousOn_const
        fun p hp => ⟨?_, ?_, ht⟩
      · exact mem_ball_zero_iff.mp (sphere_subset_ball' hrR hp.1)
      · exact mem_ball_zero_iff.mp hp.2
  · intro ζ hζ
    refine DifferentiableOn.const_mul ?_ _
    exact G_comp_diffOn hG (differentiableOn_const _) differentiableOn_id
      (differentiableOn_const _) fun x hx =>
        ⟨mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ), mem_ball_zero_iff.mp hx, ht⟩

theorem eA_diff_t (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R) (m : ℕ) {w1 : ℂ}
    (hw1 : ‖w1‖ < R) : DifferentiableOn ℂ (fun t => eA G r m w1 t) (strip s) := by
  unfold eA cI
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_circleIntegral_of_holo (φ := fun ζ t => (ζ ^ (m + 1))⁻¹ * G ![ζ, w1] t)
    (isOpen_strip' s) hr ?_ ?_
  · refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_fst.pow _).inv₀ fun p hp =>
        pow_ne_zero _ (ne_zero_of_mem_sphere' hr hp.1)
    · refine G_comp_contOn hG continuousOn_fst continuousOn_const continuousOn_snd
        fun p hp => ⟨?_, hw1, hp.2⟩
      exact mem_ball_zero_iff.mp (sphere_subset_ball' hrR hp.1)
  · intro ζ hζ
    refine DifferentiableOn.const_mul ?_ _
    exact G_comp_diffOn hG (differentiableOn_const _) (differentiableOn_const _)
      differentiableOn_id fun x hx =>
        ⟨mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ), hw1, hx⟩

theorem slice0_diff (hG : IsTPHam G R s) {w1 t : ℂ} (hw1 : ‖w1‖ < R) (ht : t ∈ strip s) :
    DifferentiableOn ℂ (fun ζ => G ![ζ, w1] t) (ball 0 R) :=
  G_comp_diffOn hG differentiableOn_id (differentiableOn_const _) (differentiableOn_const _)
    fun _ hx => ⟨mem_ball_zero_iff.mp hx, hw1, ht⟩

theorem eA_bound (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R)
    (hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ M) (m : ℕ) {w1 t : ℂ} (hw1 : ‖w1‖ < R)
    (ht : t ∈ strip s) : ‖eA G r m w1 t‖ ≤ M / r ^ m := by
  refine norm_cI_le hr ((slice0_diff hG hw1 ht).continuousOn.mono (sphere_subset_ball' hrR))
    (fun ζ hζ => hM _ (vec2_norm_lt (mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ)) hw1) _ ht) m

theorem eA_per (hG : IsTPHam G R s) (m : ℕ) (w1 t : ℂ) :
    eA G r m w1 (t + 2 * π) = eA G r m w1 t := by
  simp [eA, hG.per]

theorem eB_holPer (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R)
    (hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ M) (m n : ℕ) : HolPer (eB G r m n) s where
  holo := by
    unfold eB cI
    refine DifferentiableOn.const_mul ?_ _
    refine differentiableOn_circleIntegral_of_holo
      (φ := fun w1 t => (w1 ^ (n + 1))⁻¹ * eA G r m w1 t) (isOpen_strip' s) hr ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · exact (continuousOn_fst.pow _).inv₀ fun p hp =>
          pow_ne_zero _ (ne_zero_of_mem_sphere' hr hp.1)
      · exact (eA_contOn hG hr hrR m).mono
          (Set.prod_mono (sphere_subset_ball' hrR) subset_rfl)
    · intro ζ hζ
      exact (eA_diff_t hG hr hrR m (mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ))).const_mul _
  per := fun t => by simp [eB, eA_per hG]
  bdd := ⟨M / r ^ m / r ^ n, fun t ht =>
    norm_cI_le hr ((eA_diff_w1 hG hr hrR m ht).continuousOn.mono (sphere_subset_ball' hrR))
      (fun ζ hζ => eA_bound hG hr hrR hM m
        (mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ)) ht) n⟩

theorem term_le {M r a b c : ℝ} (hM0 : 0 ≤ M) (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbc : b ≤ c) (m k : ℕ) :
    M / r ^ m * (b / r) ^ k * a ^ m ≤ M / r ^ (m + k) * c ^ (m + k) := by
  have e : M / r ^ m * (b / r) ^ k * a ^ m = M / r ^ (m + k) * (a ^ m * b ^ k) := by
    rw [div_pow, pow_add]; field_simp
  have hc : 0 ≤ c := ha.trans hac
  rw [e, pow_add c]
  gcongr

theorem eC_bound (hG : IsTPHam G R s) (hr : 0 < r) (hrR : r < R)
    (hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ M) {w : C2} (hw : ‖w‖ < r / 2) {t : ℂ}
    (ht : t ∈ strip s) :
    ‖G w t - poly4 (fun m n => eC G r m n t) w‖ ≤ 12 * M / r ^ 5 * ‖w‖ ^ 5 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM 0 (show ‖(0 : C2)‖ < R by rw [norm_zero]; linarith) t ht)
  have h0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have h1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  have hw0 : ‖w 0‖ ≤ r / 2 := by linarith
  have hw1 : ‖w 1‖ ≤ r / 2 := by linarith
  have hw1R : ‖w 1‖ < R := by linarith
  have T1 := taylor_circle hr hrR (slice0_diff hG hw1R ht)
    (fun ζ hζ => hM _ (vec2_norm_lt (mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ)) hw1R) _ ht)
    5 hw0
  have T2 : ∀ m, ‖eA G r m (w 1) t - ∑ n ∈ Finset.range (5 - m), eB G r m n t * w 1 ^ n‖ ≤
      2 * (M / r ^ m) * (‖w 1‖ / r) ^ (5 - m) := fun m =>
    taylor_circle hr hrR (eA_diff_w1 hG hr hrR m ht)
      (fun ζ hζ => eA_bound hG hr hrR hM m (mem_ball_zero_iff.mp (sphere_subset_ball' hrR hζ)) ht)
      (5 - m) hw1
  have hpoly : poly4 (fun m n => eC G r m n t) w =
      ∑ m ∈ Finset.range 5, (∑ n ∈ Finset.range (5 - m), eB G r m n t * w 1 ^ n) * w 0 ^ m := by
    unfold poly4
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : m + n ≤ 4 := by
      simp only [Finset.mem_range] at hm hn; omega
    simp only [eC, this, ↓reduceIte]
    ring
  have hGw : G w t = G ![w 0, w 1] t := by rw [vec2_eta]
  have hdec : G w t - poly4 (fun m n => eC G r m n t) w =
      (G ![w 0, w 1] t - ∑ m ∈ Finset.range 5, eA G r m (w 1) t * w 0 ^ m) +
      ∑ m ∈ Finset.range 5,
        (eA G r m (w 1) t - ∑ n ∈ Finset.range (5 - m), eB G r m n t * w 1 ^ n) * w 0 ^ m := by
    rw [hGw, hpoly]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  have hX : ‖G ![w 0, w 1] t - ∑ m ∈ Finset.range 5, eA G r m (w 1) t * w 0 ^ m‖ ≤
      2 * (M / r ^ 5 * ‖w‖ ^ 5) := by
    refine T1.trans ?_
    have := term_le hM0 hr (norm_nonneg (w 1)) (norm_nonneg (w 0)) h1 h0 0 5
    simp only [pow_zero, div_one, mul_one, zero_add] at this
    linarith
  have hY : ∀ m ∈ Finset.range 5,
      ‖(eA G r m (w 1) t - ∑ n ∈ Finset.range (5 - m), eB G r m n t * w 1 ^ n) * w 0 ^ m‖ ≤
      2 * (M / r ^ 5 * ‖w‖ ^ 5) := by
    intro m hm
    have hm5 : m + (5 - m) = 5 := by simp only [Finset.mem_range] at hm; omega
    rw [norm_mul, norm_pow]
    have := term_le hM0 hr (norm_nonneg (w 0)) (norm_nonneg (w 1)) h0 h1 m (5 - m)
    rw [hm5] at this
    calc _ ≤ 2 * (M / r ^ m) * (‖w 1‖ / r) ^ (5 - m) * ‖w 0‖ ^ m := by
          gcongr; exact T2 m
      _ ≤ _ := by linarith
  have hS := (norm_sum_le _ _).trans (Finset.sum_le_sum hY)
  rw [Finset.sum_const, Finset.card_range] at hS
  have e : 12 * M / r ^ 5 * ‖w‖ ^ 5 = 2 * (M / r ^ 5 * ‖w‖ ^ 5) + 5 • (2 * (M / r ^ 5 * ‖w‖ ^ 5)) := by
    rw [nsmul_eq_mul]; push_cast; ring
  rw [e]
  gcongr

theorem poly4_sub_conj (a : ℕ → ℕ → ℂ) (x y : ℝ) :
    poly4 (fun m n => a m n - conj (a m n)) ![(x : ℂ), (y : ℂ)] =
      poly4 a ![(x : ℂ), (y : ℂ)] - conj (poly4 a ![(x : ℂ), (y : ℂ)]) := by
  simp [poly4, Finset.sum_range_succ, map_add, map_mul, map_pow, Complex.conj_ofReal]
  ring

theorem eB_real (hG : IsTPHam G R s) (hs : 0 < s) (hr : 0 < r) (hrR : r < R)
    (hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ M) (m n : ℕ) (h4 : m + n ≤ 4) (x : ℝ) :
    (eB G r m n x).im = 0 := by
  have ht : (x : ℂ) ∈ strip s := by simp [strip, hs]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM 0 (show ‖(0 : C2)‖ < R by rw [norm_zero]; linarith) _ ht)
  have hv := poly4_vanish (a := fun m n => eC G r m n x - conj (eC G r m n x)) (r := r / 2)
    (C := 2 * (12 * M / r ^ 5)) (j := 5) (by positivity) ?_ m n (by omega) h4
  · simp only [eC, h4, ↓reduceIte] at hv
    rw [← Complex.conj_eq_iff_im]; exact (sub_eq_zero.mp hv).symm
  intro y z hy hz
  set w : C2 := ![(y : ℂ), (z : ℂ)] with hw
  have hwn : ‖w‖ ≤ max |y| |z| := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    fin_cases i <;> simp [w]
  have hwr : ‖w‖ < r / 2 := hwn.trans_lt (max_lt hy hz)
  have hB := eC_bound hG hr hrR hM hwr ht
  have hofR : ofR !₂[y, z] = w := by
    funext i; fin_cases i <;> simp [ofR, w]
  have hreal : (G w x).im = 0 := by
    have := hG.real (!₂[y, z]) x (by rw [hofR]; linarith)
    rwa [hofR] at this
  rw [poly4_sub_conj]
  set P := poly4 (fun m n => eC G r m n x) w
  have e : P - conj P = (P - G w x) - conj (P - G w x) := by
    rw [map_sub, Complex.conj_eq_iff_im.mpr hreal]; ring
  rw [e]
  calc ‖(P - G w x) - conj (P - G w x)‖ ≤ ‖P - G w x‖ + ‖conj (P - G w x)‖ := norm_sub_le _ _
    _ = 2 * ‖G w x - P‖ := by rw [Complex.norm_conj, norm_sub_rev]; ring
    _ ≤ 2 * (12 * M / r ^ 5 * ‖w‖ ^ 5) := by gcongr
    _ ≤ 2 * (12 * M / r ^ 5) * max |y| |z| ^ 5 := by rw [← mul_assoc]; gcongr

end

/-- Taylor coefficients to order 4 of a time-periodic Hamiltonian -/
theorem extract {G : C2 → ℂ → ℂ} {R s M : ℝ} (hR : 0 < R) (hs : 0 < s) (hG : IsTPHam G R s)
    (hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ M) :
    ∃ a : ℕ → ℕ → ℂ → ℂ, (∀ m n, CoefFn (a m n) s) ∧ ∃ r > 0, ∃ C,
      Bound (fun w t => G w t - poly4 (fun m n => a m n t) w) r s C 5 := by
  refine ⟨eC G (R / 2), fun m n => ?_, R / 4, by positivity, 12 * M / (R / 2) ^ 5, ?_⟩
  · by_cases h4 : m + n ≤ 4
    · have e : eC G (R / 2) m n = eB G (R / 2) m n := funext fun t => by simp [eC, h4]
      rw [e]
      exact ⟨eB_holPer hG (by positivity) (by linarith) hM m n,
        eB_real hG hs (by positivity) (by linarith) hM m n h4⟩
    · have e : eC G (R / 2) m n = fun _ => 0 := funext fun t => by simp [eC, h4]
      rw [e]
      exact ⟨⟨differentiableOn_const _, fun _ => rfl, ⟨0, fun _ _ => by simp⟩⟩, fun _ => by simp⟩
  · intro w hw t ht
    have hw' : ‖w‖ < R / 2 / 2 := by
      have : ‖w‖ < R / 4 := hw
      linarith
    exact eC_bound hG (by positivity) (by linarith) hM hw' ht

end ABC.S4.R3Aux
