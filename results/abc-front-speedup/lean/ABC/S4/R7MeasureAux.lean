import ABC.S4.Defs

/-! Helpers for `R7_measure`: the boundary margin and the Diophantine count on the line
`ω₁ = 1`. -/

open Set Metric Real
open ABC.Poschel2001 (OmegaAlpha Delta l1norm pairZ)

noncomputable section

namespace ABC.S4.R7MeasureAux

/-- Telescoping: `∑_{n<N} 1/(x+n)² ≤ 2/x − 2/(x+N)` for `x ≥ 1`. -/
lemma sum_inv_sq_le (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (x + n) ^ 2 ≤ 2 / x - 2 / (x + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hy : 1 ≤ x + N := by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
    have key : 1 / (x + N) ^ 2 ≤ 2 / (x + N) - 2 / (x + (N + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- The `k₁`-sum for fixed `|k₀| = x`. -/
lemma inner_tsum (α x : ℝ) (hα : 0 ≤ α) (hx : x = 0 ∨ 1 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal (2 * (α / (x * (x + n) ^ 2))) ≤
      ENNReal.ofReal (4 * α * (1 / x ^ 2)) := by
  rcases hx with rfl | hx
  · simp
  · refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs := sum_inv_sq_le x hx N
    have hx0 : 0 < x := by linarith
    have hN : 0 ≤ 2 / (x + N) := by positivity
    calc ∑ i ∈ Finset.range N, 2 * (α / (x * (x + i) ^ 2))
        = (2 * α / x) * ∑ i ∈ Finset.range N, 1 / (x + i) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : 0 < x + i := by positivity
          field_simp
      _ ≤ (2 * α / x) * (2 / x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * α * (1 / x ^ 2) := by field_simp; ring

/-- `ℤ` as the image of `Bool × ℕ` (signs and absolute values). -/
def e : Bool × ℕ → ℤ := fun p => if p.1 then (p.2 : ℤ) else -(p.2 : ℤ)

lemma e_surj : Function.Surjective e := by
  intro z
  rcases Int.natAbs_eq z with h | h
  · exact ⟨(true, z.natAbs), by simp [e, ← h]⟩
  · exact ⟨(false, z.natAbs), by simp only [e]; exact h.symm⟩

lemma abs_e (p : Bool × ℕ) : |((e p : ℤ) : ℝ)| = p.2 := by
  rcases p with ⟨_ | _, n⟩ <;> simp [e]

/-- A sum over `ℤ` of a function of `|k|` is at most twice the sum over `ℕ`. -/
lemma tsum_int_le (g : ℝ → ENNReal) :
    ∑' k : ℤ, g |(k : ℝ)| ≤ 2 * ∑' n : ℕ, g n := by
  calc ∑' k : ℤ, g |(k : ℝ)| ≤ ∑' p : Bool × ℕ, g |((e p : ℤ) : ℝ)| :=
        ENNReal.tsum_le_tsum_comp_of_surjective e_surj (fun k : ℤ => g |(k : ℝ)|)
    _ = 2 * ∑' n : ℕ, g n := by
        simp only [abs_e]
        rw [ENNReal.tsum_prod', tsum_fintype, Fintype.sum_bool, two_mul]

lemma abs_int_cases (k : ℤ) : |(k : ℝ)| = 0 ∨ 1 ≤ |(k : ℝ)| := by
  rcases eq_or_ne k 0 with h | h
  · left; simp [h]
  · right; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h

/-- The union of the resonance zones `|k₀σ + k₁| < α/(|k₀| + |k₁|)²` (empty for `k₀ = 0`). -/
def U (α : ℝ) : Set ℝ :=
  ⋃ k : ℤ × ℤ, ball (-(k.2 : ℝ) / k.1) (α / (|(k.1 : ℝ)| * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) ^ 2))

lemma volume_U_le (α : ℝ) (hα : 0 ≤ α) :
    MeasureTheory.volume (U α) ≤ ENNReal.ofReal (30 * α) := by
  calc MeasureTheory.volume (U α)
      ≤ ∑' k : ℤ × ℤ, ENNReal.ofReal
          (2 * (α / (|(k.1 : ℝ)| * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) ^ 2))) := by
        refine (MeasureTheory.measure_iUnion_le _).trans (le_of_eq ?_)
        simp only [Real.volume_ball]
    _ = ∑' k₀ : ℤ, ∑' k₁ : ℤ, ENNReal.ofReal
          (2 * (α / (|(k₀ : ℝ)| * (|(k₀ : ℝ)| + |(k₁ : ℝ)|) ^ 2))) := ENNReal.tsum_prod'
    _ ≤ ∑' k₀ : ℤ, 2 * ENNReal.ofReal (4 * α * (1 / |(k₀ : ℝ)| ^ 2)) := by
        refine ENNReal.tsum_le_tsum fun k₀ => ?_
        refine (tsum_int_le (fun y => ENNReal.ofReal
          (2 * (α / (|(k₀ : ℝ)| * (|(k₀ : ℝ)| + y) ^ 2))))).trans ?_
        exact mul_le_mul_right (inner_tsum α _ hα (abs_int_cases k₀)) 2
    _ ≤ 2 * ∑' n : ℕ, 2 * ENNReal.ofReal (4 * α * (1 / (n : ℝ) ^ 2)) :=
        tsum_int_le (fun y => 2 * ENNReal.ofReal (4 * α * (1 / y ^ 2)))
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (∑' n : ℕ, 4 * α * (1 / (n : ℝ) ^ 2)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          (hasSum_zeta_two.summable.mul_left _), ENNReal.tsum_mul_left, ← mul_assoc]
        congr 1
        rw [show (4 : ℝ) = 2 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num)]
        simp
    _ = ENNReal.ofReal (4 * (4 * α * (π ^ 2 / 6))) := by
        rw [(hasSum_zeta_two.mul_left (4 * α)).tsum_eq, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (30 * α) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := pi_lt_d2
        have h2 := pi_pos
        have : π ^ 2 ≤ 11 := by nlinarith
        nlinarith

/-- Off `U α`, the point `(σ, 1)` is `(α, 2)`-Diophantine. -/
lemma delta_mem (α σ : ℝ) (hα1 : α ≤ 1) (hσ : σ ∉ U α) :
    (![σ, 1] : Fin 2 → ℝ) ∈ Delta 2 α := by
  intro k hk
  by_contra hlt
  push Not at hlt
  have hp : pairZ k ![σ, 1] = (k 0 : ℝ) * σ + k 1 := by simp [pairZ, Fin.sum_univ_two]
  have hl : l1norm k = |(k 0 : ℝ)| + |(k 1 : ℝ)| := by simp [l1norm, Fin.sum_univ_two]
  rw [hp, hl, Real.rpow_two] at hlt
  by_cases h0 : k 0 = 0
  · have h1 : k 1 ≠ 0 := by
      intro h1; apply hk; funext i; fin_cases i <;> simp [h0, h1]
    have h1' : (1 : ℝ) ≤ |(k 1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h1
    simp only [h0, Int.cast_zero, zero_mul, zero_add, abs_zero] at hlt
    have : α / |(k 1 : ℝ)| ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  · apply hσ
    refine mem_iUnion.mpr ⟨(k 0, k 1), ?_⟩
    rw [mem_ball, Real.dist_eq]
    have hk0 : (k 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have hk0' : 0 < |(k 0 : ℝ)| := abs_pos.mpr hk0
    have : σ - -(k 1 : ℝ) / k 0 = ((k 0 : ℝ) * σ + k 1) / k 0 := by field_simp; ring
    rw [this, abs_div, div_lt_iff₀ hk0']
    calc |(k 0 : ℝ) * σ + k 1| < α / (|(k 0 : ℝ)| + |(k 1 : ℝ)|) ^ 2 := hlt
      _ = α / (|(k 0 : ℝ)| * (|(k 0 : ℝ)| + |(k 1 : ℝ)|) ^ 2) * |(k 0 : ℝ)| := by
        field_simp

/-- The sup-ball of radius `α` around `(σ, 1)` lies in `OmegaE` when `σ` keeps the margin
`α(1 + |ν| + 2|b|ε)` from the ends of the interval. -/
lemma ball_subset (ν b ε α σ : ℝ) (hb : b ≠ 0) (hε : 0 < ε) (hα : 0 < α) (hα8 : α < 1 / 8)
    (hσ : |σ - (ν + 3 / 2 * b * ε)| ≤ |b| * ε / 2 - α * (1 + |ν| + 2 * |b| * ε)) :
    ball (![σ, 1] : Fin 2 → ℝ) α ⊆ OmegaE ν b ε := by
  intro x hx
  rw [mem_ball] at hx
  have h0 : |x 0 - σ| < α := by
    have := dist_le_pi_dist x ![σ, 1] 0
    rw [Real.dist_eq] at this; simpa using this.trans_lt hx
  have h1 : |x 1 - 1| < α := by
    have := dist_le_pi_dist x ![σ, 1] 1
    rw [Real.dist_eq] at this; simpa using this.trans_lt hx
  set m := ν + 3 / 2 * b * ε with hm
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hL : 0 < |b| * ε := by positivity
  have hx1 : 1 - α < x 1 := by linarith [(abs_lt.mp h1).1]
  have hx1pos : 0 < x 1 := by linarith
  have hmb : |m| ≤ |ν| + 3 / 2 * (|b| * ε) := by
    calc |m| ≤ |ν| + |3 / 2 * b * ε| := abs_add_le _ _
      _ = |ν| + 3 / 2 * (|b| * ε) := by
        rw [abs_mul, abs_mul, abs_of_pos hε]; norm_num; ring
  have key : |x 0 - m * x 1| < x 1 * (|b| * ε / 2) := by
    have e1 : x 0 - m * x 1 = (x 0 - σ) + (σ - m) - m * (x 1 - 1) := by ring
    have e2 : |m * (x 1 - 1)| ≤ |m| * α := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
    have e3 : |m| * α ≤ (|ν| + 3 / 2 * (|b| * ε)) * α :=
      mul_le_mul_of_nonneg_right hmb hα.le
    have e4 : (1 - α) * (|b| * ε) < x 1 * (|b| * ε) := mul_lt_mul_of_pos_right hx1 hL
    have a0 := abs_lt.mp h0
    have aσ := abs_le.mp hσ
    have a2 := abs_le.mp e2
    rw [e1]
    apply abs_lt.mpr
    constructor <;> nlinarith
  have hdiv : |x 0 / x 1 - m| < |b| * ε / 2 := by
    rw [show x 0 / x 1 - m = (x 0 - m * x 1) / x 1 by field_simp, abs_div,
      abs_of_pos hx1pos, div_lt_iff₀ hx1pos]
    linarith
  have hq : |(x 0 / x 1 - m) / (2 * b)| < ε / 4 := by
    rw [abs_div, abs_mul, abs_two, div_lt_iff₀ (by positivity)]
    linarith
  have aq := abs_lt.mp hq
  refine ⟨lt_trans h1 (by linarith), 3 / 4 * ε + (x 0 / x 1 - m) / (2 * b),
    ⟨by linarith, by linarith⟩, ?_⟩
  rw [hm]
  field_simp
  ring

theorem measure_bound (ν b ε α : ℝ) (hb : b ≠ 0) (hε : 0 < ε) (hα : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (|b| * ε * (1 - 8 * α) - 16 * α * (2 + |ν|)) ≤
      MeasureTheory.volume {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} := by
  have hbpos : 0 < |b| := abs_pos.mpr hb
  rcases lt_or_ge α (1 / 8) with hα8 | hα8
  swap
  · have : |b| * ε * (1 - 8 * α) - 16 * α * (2 + |ν|) ≤ 0 := by
      have : |b| * ε * (1 - 8 * α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      have : 0 ≤ 16 * α * (2 + |ν|) := by positivity
      linarith
    rw [ENNReal.ofReal_of_nonpos this]; exact zero_le
  set h := |b| * ε / 2 - α * (1 + |ν| + 2 * |b| * ε) with hh
  set m := ν + 3 / 2 * b * ε with hm
  have hsub : Icc (m - h) (m + h) \ U α ⊆
      {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} := by
    rintro σ ⟨hσJ, hσU⟩
    have hσ : |σ - m| ≤ h := abs_le.mpr ⟨by linarith [hσJ.1], by linarith [hσJ.2]⟩
    have hball := ball_subset ν b ε α σ hb hε hα hα8 hσ
    refine ⟨hball (mem_ball_self hα), delta_mem α σ hα1 hσU, ?_⟩
    intro y hy
    by_contra hlt
    push Not at hlt
    have hyb : y ∈ ball (![σ, 1] : Fin 2 → ℝ) α := by rw [mem_ball, dist_comm]; exact hlt
    exact hy.2 (interior_maximal hball isOpen_ball hyb)
  have hU := volume_U_le α hα.le
  have hJ : MeasureTheory.volume (Icc (m - h) (m + h)) = ENNReal.ofReal (2 * h) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hreal : |b| * ε * (1 - 8 * α) - 16 * α * (2 + |ν|) ≤ 2 * h - 30 * α := by
    rw [hh]
    nlinarith [mul_nonneg hα.le (abs_nonneg ν), mul_pos hα (mul_pos hbpos hε)]
  calc ENNReal.ofReal (|b| * ε * (1 - 8 * α) - 16 * α * (2 + |ν|))
      ≤ ENNReal.ofReal (2 * h - 30 * α) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * h) - ENNReal.ofReal (30 * α) := ENNReal.ofReal_sub _ (by positivity)
    _ ≤ MeasureTheory.volume (Icc (m - h) (m + h)) - MeasureTheory.volume (U α) := by
        rw [hJ]; exact tsub_le_tsub_left hU _
    _ ≤ MeasureTheory.volume (Icc (m - h) (m + h) \ U α) := MeasureTheory.le_measure_sdiff
    _ ≤ _ := MeasureTheory.measure_mono hsub

end ABC.S4.R7MeasureAux
