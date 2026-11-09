import ABC.Twist

/-! T1 helpers: 3-jets in `w, w̄` (expansion, uniqueness). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace ABC.S4.TwistConjAux

open ABC

theorem jetPoly_eq (c : ℕ → ℕ → ℂ) (w : ℂ) :
    jetPoly c w = c 0 0 + (c 1 0 * w + c 0 1 * conj w)
      + (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2)
      + (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2
        + c 0 3 * conj w ^ 3) := by
  simp only [jetPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- one-variable uniqueness: a cubic that is `o(t³)` vanishes -/
theorem cubic_eq_zero {A₀ A₁ A₂ A₃ : ℂ}
    (h : (fun t : ℝ => A₀ + A₁ * t + A₂ * t ^ 2 + A₃ * t ^ 3) =o[𝓝 0] fun t : ℝ => t ^ 3) :
    A₀ = 0 ∧ A₁ = 0 ∧ A₂ = 0 ∧ A₃ = 0 := by
  set P : ℝ → ℂ := fun t : ℝ => A₀ + A₁ * t + A₂ * t ^ 2 + A₃ * t ^ 3 with hP
  -- for every `ε`, some `0 < t ≤ 1` has `‖P (k t)‖ ≤ ε (k t)³`, `k = 1..4`
  have key : ∀ ε > 0, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ k ∈ ({1, 2, 3, 4} : Finset ℝ),
      ‖P (k * t)‖ ≤ ε * (k * t) ^ 3 := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (h.def hε)
    refine ⟨min (δ / 8) 1, by positivity, min_le_right _ _, fun k hk => ?_⟩
    have hk0 : 0 < k := by simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> norm_num
    have hk4 : k ≤ 4 := by simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> norm_num
    have ht : 0 < min (δ / 8) 1 := by positivity
    have := hb (y := k * min (δ / 8) 1) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      calc k * min (δ / 8) 1 ≤ 4 * (δ / 8) := by
            gcongr; exact min_le_left _ _
        _ < δ := by linarith)
    have hpos : (0:ℝ) < k * min (δ / 8) 1 := by positivity
    rwa [norm_pow, Real.norm_eq_abs, abs_of_pos hpos] at this
  -- each coefficient is a fixed combination of the four values
  have comb : ∀ (μ : Fin 4 → ℝ) (d : ℕ) (A : ℂ),
      (∀ t : ℝ, A * (t : ℂ) ^ d = ∑ i : Fin 4, (μ i : ℂ) * P (((i : ℕ) + 1 : ℝ) * t)) →
      d ≤ 3 → A = 0 := by
    intro μ d A hA hd
    set K : ℝ := ∑ i : Fin 4, |μ i| * (((i : ℕ) + 1 : ℝ)) ^ 3 with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
    refine norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨t, ht0, ht1, hb⟩ := key (ε / (K + 1)) (by positivity)
    have h1 : ‖A‖ * t ^ d ≤ ε / (K + 1) * K * t ^ 3 := by
      have e := congrArg norm (hA t)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at e
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      rw [hK, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hi : ((i : ℕ) + 1 : ℝ) ∈ ({1, 2, 3, 4} : Finset ℝ) := by
        fin_cases i <;> norm_num
      have := hb _ hi
      calc |μ i| * ‖P (((i : ℕ) + 1 : ℝ) * t)‖
          ≤ |μ i| * (ε / (K + 1) * (((i : ℕ) + 1 : ℝ) * t) ^ 3) := by gcongr
        _ = ε / (K + 1) * (|μ i| * (((i : ℕ) + 1 : ℝ)) ^ 3) * t ^ 3 := by ring
    have h2 : t ^ 3 ≤ t ^ d := pow_le_pow_of_le_one ht0.le ht1 hd
    have h3 : ε / (K + 1) * K ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    have htd : 0 < t ^ d := by positivity
    have : ‖A‖ * t ^ d ≤ ε * t ^ d := by
      calc ‖A‖ * t ^ d ≤ ε / (K + 1) * K * t ^ 3 := h1
        _ ≤ ε * t ^ 3 := by gcongr
        _ ≤ ε * t ^ d := by gcongr
    have := le_of_mul_le_mul_right this htd
    linarith
  refine ⟨comb ![4, -6, 4, -1] 0 A₀ (fun t => ?_) (by norm_num),
    comb ![-13/3, 19/2, -7, 11/6] 1 A₁ (fun t => ?_) (by norm_num),
    comb ![3/2, -4, 7/2, -1] 2 A₂ (fun t => ?_) (by norm_num),
    comb ![-1/6, 1/2, -1/2, 1/6] 3 A₃ (fun t => ?_) (by norm_num)⟩ <;>
  · simp only [hP, Fin.sum_univ_four]
    push_cast
    norm_num
    ring


theorem jetPoly_ray (c : ℕ → ℕ → ℂ) (u : ℂ) (t : ℝ) :
    jetPoly c ((t : ℂ) * u) = c 0 0 + (c 1 0 * u + c 0 1 * conj u) * t
      + (c 2 0 * u ^ 2 + c 1 1 * u * conj u + c 0 2 * conj u ^ 2) * t ^ 2
      + (c 3 0 * u ^ 3 + c 2 1 * u ^ 2 * conj u + c 1 2 * u * conj u ^ 2
        + c 0 3 * conj u ^ 3) * t ^ 3 := by
  rw [jetPoly_eq, map_mul, Complex.conj_ofReal]; ring

theorem ray_coeffs {c : ℕ → ℕ → ℂ} (h : (fun w => jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ 3)
    (u : ℂ) : c 0 0 = 0 ∧ c 1 0 * u + c 0 1 * conj u = 0 ∧
      c 2 0 * u ^ 2 + c 1 1 * u * conj u + c 0 2 * conj u ^ 2 = 0 ∧
      c 3 0 * u ^ 3 + c 2 1 * u ^ 2 * conj u + c 1 2 * u * conj u ^ 2 + c 0 3 * conj u ^ 3 = 0 := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * u) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun t : ℝ => (t : ℂ) * u) := by fun_prop
    simpa using this.tendsto 0
  have h1 := h.comp_tendsto ht
  have h2 : (fun t : ℝ => ‖(t : ℂ) * u‖ ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    refine IsBigO.of_bound (‖u‖ ^ 3) (Eventually.of_forall fun t => ?_)
    simp [abs_mul, mul_comm, mul_pow]
  have h3 := h1.trans_isBigO h2
  simp only [Function.comp_def, jetPoly_ray] at h3
  exact cubic_eq_zero (A₀ := c 0 0) h3

theorem jet_zero {c : ℕ → ℕ → ℂ} (h : (fun w => jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ 3) :
    c 0 0 = 0 ∧ c 1 0 = 0 ∧ c 0 1 = 0 ∧ c 2 0 = 0 ∧ c 1 1 = 0 ∧ c 0 2 = 0 ∧
      c 3 0 = 0 ∧ c 2 1 = 0 ∧ c 1 2 = 0 ∧ c 0 3 = 0 := by
  obtain ⟨h0, a1, a2, a3⟩ := ray_coeffs h 1
  obtain ⟨-, b1, b2, b3⟩ := ray_coeffs h Complex.I
  obtain ⟨-, -, c2, c3⟩ := ray_coeffs h (1 + Complex.I)
  obtain ⟨-, -, -, d3⟩ := ray_coeffs h (1 - Complex.I)
  simp only [map_one, map_add, map_sub, Complex.conj_I, one_pow, mul_one] at a1 a2 a3 b1 b2 b3 c2 c3 d3
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (norm := skip) (1/2 : ℂ) * a1 - Complex.I / 2 * b1
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/2 : ℂ) * a1 + Complex.I / 2 * b1
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 + Complex.I/4) * a2 + (-1/4 + Complex.I/4) * b2 - Complex.I/4 * c2
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/2 : ℂ) * a2 + (1/2 : ℂ) * b2
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 - Complex.I/4) * a2 + (-1/4 - Complex.I/4) * b2 + Complex.I/4 * c2
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 : ℂ) * a3 + Complex.I/4 * b3 + (-1/16 - Complex.I/16) * c3 + (-1/16 + Complex.I/16) * d3
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 : ℂ) * a3 - Complex.I/4 * b3 + (1/16 - Complex.I/16) * c3 + (1/16 + Complex.I/16) * d3
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 : ℂ) * a3 + Complex.I/4 * b3 + (1/16 + Complex.I/16) * c3 + (1/16 - Complex.I/16) * d3
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf
  · linear_combination (norm := skip) (1/4 : ℂ) * a3 - Complex.I/4 * b3 + (-1/16 + Complex.I/16) * c3 + (-1/16 - Complex.I/16) * d3
    ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring_nf


/-! ### `O(|w|ⁿ)` bookkeeping -/

/-- `f = O(|w|ⁿ)` at `0` -/
def BO (n : ℕ) (f : ℂ → ℂ) : Prop := f =O[𝓝 (0 : ℂ)] fun w => ‖w‖ ^ n

theorem pow_isBigO {m n : ℕ} (h : m ≤ n) :
    (fun w : ℂ => ‖w‖ ^ n) =O[𝓝 (0 : ℂ)] fun w => ‖w‖ ^ m := by
  rcases h.lt_or_eq with h | rfl
  · exact (isLittleO_norm_pow_norm_pow h).isBigO
  · exact isBigO_refl _ _

theorem BO.congr {n : ℕ} {f g : ℂ → ℂ} (hf : BO n f) (h : ∀ w, f w = g w) : BO n g := by
  have : f = g := funext h
  rwa [← this]

theorem BO.idx {m n : ℕ} {f : ℂ → ℂ} (hf : BO m f) (h : m = n) : BO n f := h ▸ hf

theorem BO.add {n : ℕ} {f g : ℂ → ℂ} (hf : BO n f) (hg : BO n g) :
    BO n (fun w => f w + g w) := IsBigO.add hf hg

theorem BO.sub {n : ℕ} {f g : ℂ → ℂ} (hf : BO n f) (hg : BO n g) :
    BO n (fun w => f w - g w) := IsBigO.sub hf hg

theorem BO.mul {m n : ℕ} {f g : ℂ → ℂ} (hf : BO m f) (hg : BO n g) :
    BO (m + n) (fun w => f w * g w) := by
  have := IsBigO.mul hf hg
  simpa only [BO, pow_add] using this

theorem BO.const_mul {n : ℕ} {f : ℂ → ℂ} (c : ℂ) (hf : BO n f) : BO n (fun w => c * f w) :=
  IsBigO.const_mul_left hf c

theorem BO.mono {m n : ℕ} {f : ℂ → ℂ} (h : m ≤ n) (hf : BO n f) : BO m f :=
  IsBigO.trans hf (pow_isBigO h)

theorem BO.conj {n : ℕ} {f : ℂ → ℂ} (hf : BO n f) : BO n (fun w => conj (f w)) := by
  refine isBigO_norm_left.1 ?_
  simpa only [Complex.norm_conj] using hf.norm_left

theorem BO.zero (n : ℕ) : BO n (fun _ => 0) := isBigO_zero _ _

theorem BO_mono_ (c : ℂ) (j k : ℕ) : BO (j + k) (fun w => c * w ^ j * conj w ^ k) := by
  refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun w => ?_)
  simp [norm_mul, norm_pow, Complex.norm_conj, pow_add, mul_assoc]

theorem BO.isLittleO {m n : ℕ} {f : ℂ → ℂ} (hf : BO n f) (h : m < n) :
    f =o[𝓝 (0 : ℂ)] fun w => ‖w‖ ^ m :=
  IsBigO.trans_isLittleO hf (isLittleO_norm_pow_norm_pow h)

theorem BO.prod_diff {m n : ℕ} {a b A B : ℂ → ℂ} (h1 : BO (m + 1) (fun w => a w - A w))
    (h2 : BO (n + 1) (fun w => b w - B w)) (ha : BO m a) (hB : BO n B) :
    BO (m + n + 1) (fun w => a w * b w - A w * B w) := by
  have e1 := (ha.mul h2).idx (by omega : m + (n + 1) = m + n + 1)
  have e2 := (h1.mul hB).idx (by omega : m + 1 + n = m + n + 1)
  exact (e1.add e2).congr fun w => by ring

/-! ### composition of jets -/

/-- the 3-jet of `jetPoly q ∘ jetPoly p` when `p 0 0 = p 0 1 = 0` -/
def comp (q p : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => q 0 0
  | 1, 0 => q 1 0 * p 1 0
  | 0, 1 => q 0 1 * conj (p 1 0)
  | 2, 0 => q 2 0 * p 1 0 ^ 2 + q 1 0 * p 2 0 + q 0 1 * conj (p 0 2)
  | 1, 1 => q 1 1 * p 1 0 * conj (p 1 0) + q 1 0 * p 1 1 + q 0 1 * conj (p 1 1)
  | 0, 2 => q 0 2 * conj (p 1 0) ^ 2 + q 1 0 * p 0 2 + q 0 1 * conj (p 2 0)
  | 3, 0 => q 3 0 * p 1 0 ^ 3 + 2 * q 2 0 * p 1 0 * p 2 0 + q 1 1 * p 1 0 * conj (p 0 2)
      + q 1 0 * p 3 0 + q 0 1 * conj (p 0 3)
  | 2, 1 => q 2 1 * p 1 0 ^ 2 * conj (p 1 0) + 2 * q 2 0 * p 1 0 * p 1 1
      + q 1 1 * p 1 0 * conj (p 1 1) + q 1 1 * p 2 0 * conj (p 1 0) + q 1 0 * p 2 1
      + 2 * q 0 2 * conj (p 0 2) * conj (p 1 0) + q 0 1 * conj (p 1 2)
  | 1, 2 => 2 * q 2 0 * p 0 2 * p 1 0 + q 1 2 * p 1 0 * conj (p 1 0) ^ 2
      + q 1 1 * p 1 0 * conj (p 2 0) + q 1 1 * p 1 1 * conj (p 1 0) + q 1 0 * p 1 2
      + 2 * q 0 2 * conj (p 1 0) * conj (p 1 1) + q 0 1 * conj (p 2 1)
  | 0, 3 => q 1 1 * p 0 2 * conj (p 1 0) + q 1 0 * p 0 3 + q 0 3 * conj (p 1 0) ^ 3
      + 2 * q 0 2 * conj (p 1 0) * conj (p 2 0) + q 0 1 * conj (p 3 0)
  | _, _ => 0

theorem BO_jetPoly (p : ℕ → ℕ → ℂ) (hp0 : p 0 0 = 0) : BO 1 (jetPoly p) := by
  have h1 := (BO_mono_ (p 1 0) 1 0).add (BO_mono_ (p 0 1) 0 1)
  have h2 := (((BO_mono_ (p 2 0) 2 0).add (BO_mono_ (p 1 1) 1 1)).add
    (BO_mono_ (p 0 2) 0 2)).mono (by norm_num : 1 ≤ 2)
  have h3 := ((((BO_mono_ (p 3 0) 3 0).add (BO_mono_ (p 2 1) 2 1)).add
    (BO_mono_ (p 1 2) 1 2)).add (BO_mono_ (p 0 3) 0 3)).mono (by norm_num : 1 ≤ 3)
  refine ((h1.add h2).add h3).congr fun w => ?_
  rw [jetPoly_eq, hp0]; ring

theorem poly_comp (q p : ℕ → ℕ → ℂ) (hp0 : p 0 0 = 0) (hp1 : p 0 1 = 0) :
    BO 4 (fun w => jetPoly q (jetPoly p w) - jetPoly (comp q p) w) := by
  set P1 : ℂ → ℂ := fun w => p 1 0 * w ^ 1 * conj w ^ 0
  set P2 : ℂ → ℂ := fun w => p 2 0 * w ^ 2 * conj w ^ 0 + p 1 1 * w ^ 1 * conj w ^ 1
    + p 0 2 * w ^ 0 * conj w ^ 2
  set P3 : ℂ → ℂ := fun w => p 3 0 * w ^ 3 * conj w ^ 0 + p 2 1 * w ^ 2 * conj w ^ 1
    + p 1 2 * w ^ 1 * conj w ^ 2 + p 0 3 * w ^ 0 * conj w ^ 3
  set Q1 : ℂ → ℂ := fun w => conj (p 1 0) * w ^ 0 * conj w ^ 1
  set Q2 : ℂ → ℂ := fun w => conj (p 2 0) * w ^ 0 * conj w ^ 2
    + conj (p 1 1) * w ^ 1 * conj w ^ 1 + conj (p 0 2) * w ^ 2 * conj w ^ 0
  set Q3 : ℂ → ℂ := fun w => conj (p 3 0) * w ^ 0 * conj w ^ 3
    + conj (p 2 1) * w ^ 1 * conj w ^ 2 + conj (p 1 2) * w ^ 2 * conj w ^ 1
    + conj (p 0 3) * w ^ 3 * conj w ^ 0
  set z : ℂ → ℂ := fun w => jetPoly p w
  set zb : ℂ → ℂ := fun w => conj (jetPoly p w)
  have hz : ∀ w, z w = P1 w + P2 w + P3 w := fun w => by
    simp only [z, P1, P2, P3]; rw [jetPoly_eq, hp0, hp1]; ring
  have hzb : ∀ w, zb w = Q1 w + Q2 w + Q3 w := fun w => by
    simp only [zb, Q1, Q2, Q3]; rw [jetPoly_eq, hp0, hp1]
    simp only [map_add, map_mul, map_pow, map_zero, Complex.conj_conj]; ring
  have bP1 : BO 1 P1 := BO_mono_ _ 1 0
  have bQ1 : BO 1 Q1 := BO_mono_ _ 0 1
  have bP2 : BO 2 P2 := ((BO_mono_ _ 2 0).add (BO_mono_ _ 1 1)).add (BO_mono_ _ 0 2)
  have bQ2 : BO 2 Q2 := ((BO_mono_ _ 0 2).add (BO_mono_ _ 1 1)).add (BO_mono_ _ 2 0)
  have bP3 : BO 3 P3 :=
    (((BO_mono_ _ 3 0).add (BO_mono_ _ 2 1)).add (BO_mono_ _ 1 2)).add (BO_mono_ _ 0 3)
  have bQ3 : BO 3 Q3 :=
    (((BO_mono_ _ 0 3).add (BO_mono_ _ 1 2)).add (BO_mono_ _ 2 1)).add (BO_mono_ _ 3 0)
  have bD : BO 2 (fun w => z w - P1 w) :=
    (bP2.add (bP3.mono (by norm_num))).congr fun w => by rw [hz]; ring
  have bDb : BO 2 (fun w => zb w - Q1 w) :=
    (bQ2.add (bQ3.mono (by norm_num))).congr fun w => by rw [hzb]; ring
  have bz : BO 1 z := (bP1.add (bD.mono (by norm_num))).congr fun w => by ring
  have bzb : BO 1 zb := (bQ1.add (bDb.mono (by norm_num))).congr fun w => by ring
  -- quadratic and cubic monomials of `z`
  have s20 : BO 3 (fun w => z w * z w - P1 w * P1 w) := BO.prod_diff (m := 1) (n := 1) bD bD bz bP1
  have s11 : BO 3 (fun w => z w * zb w - P1 w * Q1 w) := BO.prod_diff (m := 1) (n := 1) bD bDb bz bQ1
  have s02 : BO 3 (fun w => zb w * zb w - Q1 w * Q1 w) :=
    BO.prod_diff (m := 1) (n := 1) bDb bDb bzb bQ1
  have c30 := BO.prod_diff (m := 2) (n := 1) s20 bD (bz.mul bz) bP1
  have c21 := BO.prod_diff (m := 2) (n := 1) s20 bDb (bz.mul bz) bQ1
  have c12 := BO.prod_diff (m := 2) (n := 1) s02 bD (bzb.mul bzb) bP1
  have c03 := BO.prod_diff (m := 2) (n := 1) s02 bDb (bzb.mul bzb) bQ1
  have q20 : BO 4 (fun w => 2 * P1 w * P3 w + (z w - P1 w) * (z w - P1 w)) :=
    (((bP1.mul bP3).const_mul 2).add (bD.mul bD)).congr fun w => by ring
  have q11 : BO 4 (fun w => P1 w * Q3 w + P3 w * Q1 w + (z w - P1 w) * (zb w - Q1 w)) :=
    (((bP1.mul bQ3).add ((bP3.mul bQ1).idx (by norm_num))).add (bD.mul bDb)).congr
      fun w => by ring
  have q02 : BO 4 (fun w => 2 * Q1 w * Q3 w + (zb w - Q1 w) * (zb w - Q1 w)) :=
    (((bQ1.mul bQ3).const_mul 2).add (bDb.mul bDb)).congr fun w => by ring
  have R := (((((((q20.const_mul (q 2 0)).add (q11.const_mul (q 1 1))).add
    (q02.const_mul (q 0 2))).add (c30.const_mul (q 3 0))).add (c21.const_mul (q 2 1))).add
    (c12.const_mul (q 1 2))).add (c03.const_mul (q 0 3)))
  refine R.congr fun w => ?_
  have e1 := hz w
  have e2 := hzb w
  simp only [z, zb, P1, P2, P3, Q1, Q2, Q3] at e1 e2 ⊢
  rw [jetPoly_eq q, jetPoly_eq (comp q p)]
  simp only [comp]
  generalize jetPoly p w = Z at e1 e2 ⊢
  linear_combination (-(q 1 0) - 2 * q 2 0 * (p 1 0 * w) - q 1 1 * (conj (p 1 0) * conj w)) * e1
    + (-(q 0 1) - q 1 1 * (p 1 0 * w) - 2 * q 0 2 * (conj (p 1 0) * conj w)) * e2


theorem conj_contDiff : ContDiff ℝ ⊤ (fun w : ℂ => conj w) := Complex.conjCLE.contDiff

theorem jetPoly_contDiff (c : ℕ → ℕ → ℂ) : ContDiff ℝ ⊤ (jetPoly c) := by
  have hc := conj_contDiff
  have : jetPoly c = fun w => c 0 0 + (c 1 0 * w + c 0 1 * conj w)
      + (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2)
      + (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2
        + c 0 3 * conj w ^ 3) := funext (jetPoly_eq c)
  rw [this]
  fun_prop

theorem tendsto_norm_pow (n : ℕ) : Tendsto (fun w : ℂ => ‖w‖ ^ (n + 1)) (𝓝 0) (𝓝 0) := by
  have : Continuous (fun w : ℂ => ‖w‖ ^ (n + 1)) := by fun_prop
  simpa using this.tendsto 0

theorem comp_jet {F G : ℂ → ℂ} {p q : ℕ → ℕ → ℂ} (hp0 : p 0 0 = 0) (hp1 : p 0 1 = 0)
    (hF : (fun w => F w - jetPoly p w) =o[𝓝 0] fun w => ‖w‖ ^ 3)
    (hG : (fun z => G z - jetPoly q z) =o[𝓝 0] fun z => ‖z‖ ^ 3) :
    (fun w => G (F w) - jetPoly (comp q p) w) =o[𝓝 0] fun w => ‖w‖ ^ 3 := by
  have bFP : BO 3 (fun w => F w - jetPoly p w) := hF.isBigO
  have bF : BO 1 F := ((bFP.mono (by norm_num)).add (BO_jetPoly p hp0)).congr fun w => by ring
  have tF : Tendsto F (𝓝 0) (𝓝 0) := IsBigO.trans_tendsto bF (tendsto_norm_pow 0)
  have tP : Tendsto (jetPoly p) (𝓝 0) (𝓝 0) :=
    IsBigO.trans_tendsto (BO_jetPoly p hp0) (tendsto_norm_pow 0)
  -- `G ∘ F` versus `jetPoly q ∘ F`
  have t1 : (fun w => G (F w) - jetPoly q (F w)) =o[𝓝 0] fun w => ‖w‖ ^ 3 := by
    have h1 := hG.comp_tendsto tF
    have h2 : (fun w => ‖F w‖ ^ 3) =O[𝓝 0] fun w => ‖w‖ ^ 3 := by
      have := (IsBigO.norm_left (bF : F =O[𝓝 0] fun w => ‖w‖ ^ 1)).pow 3
      simpa only [pow_one] using this
    exact h1.trans_isBigO h2
  -- Lipschitz `jetPoly q` near `0`
  have t2 : (fun w => jetPoly q (F w) - jetPoly q (jetPoly p w)) =o[𝓝 0]
      fun w => ‖w‖ ^ 3 := by
    obtain ⟨K, t, ht, hL⟩ :=
      ((jetPoly_contDiff q).contDiffAt (x := (0 : ℂ))).of_le (by norm_num)
        |>.exists_lipschitzOnWith
    have ht' : t ∈ 𝓝 (jetPoly p 0) := by
      have : jetPoly p 0 = 0 := by rw [jetPoly_eq, hp0]; simp
      rwa [this]
    have hev : ∀ᶠ w in 𝓝 (0 : ℂ), F w ∈ t ∧ jetPoly p w ∈ t :=
      (tF.eventually ht).and (tP.eventually ht)
    have hO : (fun w => jetPoly q (F w) - jetPoly q (jetPoly p w)) =O[𝓝 0]
        fun w => F w - jetPoly p w := by
      refine IsBigO.of_bound K (hev.mono fun w hw => ?_)
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hL.dist_le_mul _ hw.1 _ hw.2
    exact hO.trans_isLittleO hF
  have t3 := (poly_comp q p hp0 hp1).isLittleO (m := 3) (by norm_num)
  refine ((t1.add t2).add t3).congr_left fun w => ?_
  ring

theorem jetPoly_sub (c d : ℕ → ℕ → ℂ) (w : ℂ) :
    jetPoly (fun j k => c j k - d j k) w = jetPoly c w - jetPoly d w := by
  rw [jetPoly_eq, jetPoly_eq, jetPoly_eq]; ring

/-- two 3-jets of (germs of) the same function agree -/
theorem jet_eq {F G : ℂ → ℂ} {c d : ℕ → ℕ → ℂ} (hFG : F =ᶠ[𝓝 0] G)
    (hF : (fun w => F w - jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ 3)
    (hG : (fun w => G w - jetPoly d w) =o[𝓝 0] fun w => ‖w‖ ^ 3) :
    c 0 0 = d 0 0 ∧ c 1 0 = d 1 0 ∧ c 0 1 = d 0 1 ∧ c 2 0 = d 2 0 ∧ c 1 1 = d 1 1 ∧
      c 0 2 = d 0 2 ∧ c 3 0 = d 3 0 ∧ c 2 1 = d 2 1 ∧ c 1 2 = d 1 2 ∧ c 0 3 = d 0 3 := by
  have h : (fun w => jetPoly (fun j k => c j k - d j k) w) =o[𝓝 0] fun w => ‖w‖ ^ 3 := by
    refine (hG.sub hF).congr' (hFG.mono fun w hw => ?_) EventuallyEq.rfl
    beta_reduce; rw [jetPoly_sub, hw]; ring
  have := jet_zero h
  simp only [sub_eq_zero] at this
  exact this

/-- the constant term of a jet is the value -/
theorem jet_val {F : ℂ → ℂ} {c : ℕ → ℕ → ℂ} {n : ℕ}
    (hF : (fun w => F w - jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ (n + 1)) : F 0 = c 0 0 := by
  have h : (fun w => F w - jetPoly c w) =O[𝓝 0] fun x : ℂ => ‖x - 0‖ ^ (n + 1) := by
    simpa only [sub_zero] using hF.isBigO
  have := h.eq_zero_of_norm_pow (Nat.succ_ne_zero n)
  rw [jetPoly_eq] at this; simpa [sub_eq_zero] using this

end ABC.S4.TwistConjAux
