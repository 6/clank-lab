import EKG.PartBRoughness

/-! Eventual scalar discharge for every canonical missing composite.
Part B chooses its own fixed multiplier, with harmless extra stride slack;
the later assembly uses Part A's endpoint without sharing Part A's internal
multiplier. Every choice precedes both the observation time and the hole.
-/

namespace EKG.PartB

open Real Filter

structure HoleParameters (delta : ℝ) (t h M : ℕ) (B : ℝ) : Prop where
  factor_prime : h.minFac.Prime
  factor_dvd : h.minFac ∣ h
  factor_sq : h.minFac ^ 2 ≤ h
  gap_upper : (frontier canonical t : ℝ) - (h : ℝ) ≤
    1604 * logRate (frontier canonical t)
  scale_large : 3 < B
  multiplier_lt : (M : ℝ) < B
  cube : (frontier canonical t : ℝ) < B ^ 3
  stride : (frontier canonical t : ℝ) ≤ (2 * h.minFac * M : ℕ) * B
  rough_scale : 2 * B *
    (13 * Nat.primeCounting (Nat.sqrt (frontier canonical t)) + 724 : ℕ) ≤
      delta / 3 * logRate (frontier canonical t)

/-- At every sufficiently late prefix, every putative normalized hole
supplies all finite-injection scales, with one fixed `M=M(delta)`. -/
theorem eventually_hole_parameters (delta : ℝ) (hdelta : 0 < delta) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ᶠ t : ℕ in atTop, ∀ h : ℕ,
      2 ≤ h → ¬ h.Prime → h < frontier canonical t →
      ¬ UsedBefore canonical.a (t + 1) h →
      delta * logRate (frontier canonical t) ≤
        (frontier canonical t : ℝ) - (h : ℝ) →
      HoleParameters delta t h M
        (delta / (6 * 802) * Real.sqrt (frontier canonical t)) := by
  let alpha : ℝ := delta / 1604
  let beta : ℝ := delta / (6 * 802)
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hb : 0 < beta := by dsimp [beta]; positivity
  have hab : 0 < alpha * beta := mul_pos ha hb
  have hb3 : 0 < beta ^ 3 := pow_pos hb 3
  have halpha : 1604 * alpha = delta := by dsimp [alpha]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (alpha * beta))
  let M := N + 2
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hMN : (N : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hN' : 1 < (N : ℝ) * (alpha * beta) := (div_lt_iff₀ hab).mp hN
  have habM : 1 ≤ (alpha * beta) * M := by
    have h := mul_le_mul_of_nonneg_left hMN hab.le
    nlinarith only [h, hN']
  have hf : Tendsto (fun t => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have hroot : Tendsto (fun t => Real.sqrt (frontier canonical t)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hf
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_canonical_hole_factor_count,
    eventually_ge_atTop (8 : ℕ), hf.eventually (eventually_gt_atTop (2 : ℝ)),
    hroot.eventually (eventually_gt_atTop ((M : ℝ) / beta)),
    hroot.eventually (eventually_gt_atTop (3 / beta)),
    hroot.eventually (eventually_gt_atTop (1 / beta ^ 3))]
    with t hcount ht he2 hrootM hroot3 hrootcube
  intro h hh hnp hbelow hfree hgap
  let e : ℝ := frontier canonical t
  let q : ℝ := Real.sqrt e
  let s : ℝ := h.minFac
  let F : ℝ := (13 * Nat.primeCounting (Nat.sqrt (frontier canonical t)) + 724 : ℕ)
  let B : ℝ := beta * q
  have he : 0 < e := by dsimp [e]; linarith
  have helog : 0 < Real.log e := Real.log_pos (by dsimp [e]; linarith)
  have hq : 0 < q := Real.sqrt_pos.2 he
  have hq0 : 0 ≤ q := hq.le
  have hsq : q ^ 2 = e := Real.sq_sqrt he.le
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨hsprime, hsdvd, hssq, hbound⟩ :=
    canonical_missing_composite_geometry ht (by omega : 1 < h) hnp hbelow hfree hbelow.le
  have hssqreal : s ^ 2 ≤ (h : ℝ) := by dsimp [s]; exact_mod_cast hssq
  have hhe : (h : ℝ) ≤ e := by dsimp [e]; exact_mod_cast hbelow.le
  have hsroot : s ≤ q := Real.le_sqrt_of_sq_le (hssqreal.trans hhe)
  change e - (h : ℝ) ≤ 2 * s * F at hbound
  change F ≤ 802 * sqrtLogRate e at hcount
  have hmajor : e - (h : ℝ) ≤ 1604 * logRate e := by
    have hsf := mul_le_mul_of_nonneg_right hsroot hF0
    calc
      e - (h : ℝ) ≤ 2 * s * F := hbound
      _ ≤ 2 * q * F := by nlinarith only [hsf]
      _ ≤ 2 * q * (802 * sqrtLogRate e) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = 1604 * logRate e := by
        rw [← sqrtLogRate_mul_sqrt he.le]
        dsimp [q]
        ring
  have hupper : e - (h : ℝ) ≤ (1604 * s * q) / Real.log e := by
    calc
      e - (h : ℝ) ≤ 2 * s * F := hbound
      _ ≤ 2 * s * (802 * sqrtLogRate e) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = (1604 * s * q) / Real.log e := by dsimp [sqrtLogRate, q]; ring
  have hscaled : delta * e ≤ 1604 * s * q := by
    change delta * (e / Real.log e) ≤ e - (h : ℝ) at hgap
    rw [← mul_div_assoc] at hgap
    have hlo := (div_le_iff₀ helog).mp hgap
    have hhi := (le_div_iff₀ helog).mp hupper
    exact hlo.trans hhi
  have hcancel : (alpha * q) * (1604 * q) ≤ s * (1604 * q) := by
    calc
      (alpha * q) * (1604 * q) = delta * e := by rw [← halpha, ← hsq]; ring
      _ ≤ s * (1604 * q) := by nlinarith only [hscaled]
  have hslower : alpha * q ≤ s :=
    (mul_le_mul_iff_left₀ (show (0 : ℝ) < 1604 * q by positivity)).mp hcancel
  have hthree : 3 < B := by
    have h := (div_lt_iff₀ hb).mp hroot3
    dsimp [B, q, e]
    nlinarith only [h]
  have hMlt : (M : ℝ) < B := by
    have h := (div_lt_iff₀ hb).mp hrootM
    dsimp [B, q, e]
    nlinarith only [h]
  have hcube : e < B ^ 3 := by
    have hrootcube' : 1 < beta ^ 3 * q := by
      have h := (div_lt_iff₀ hb3).mp hrootcube
      dsimp [q, e]
      nlinarith only [h]
    have hmul := mul_lt_mul_of_pos_right hrootcube' he
    have hid : (beta ^ 3 * q) * e = B ^ 3 := by
      dsimp [B]
      rw [← hsq]
      ring
    simpa only [one_mul, hid] using hmul
  have hstride : e ≤ (2 * s * M) * B := by
    have hm := mul_le_mul_of_nonneg_right habM he.le
    have hsmul := mul_le_mul_of_nonneg_right hslower
      (show (0 : ℝ) ≤ 2 * (M : ℝ) * B by positivity)
    calc
      e ≤ (2 * ((alpha * beta) * M)) * e := by nlinarith only [hm, he]
      _ = (alpha * q) * (2 * (M : ℝ) * B) := by
        dsimp [B]
        rw [← hsq]
        ring
      _ ≤ s * (2 * (M : ℝ) * B) := hsmul
      _ = (2 * s * M) * B := by ring
  have hrough : 2 * B * F ≤ delta / 3 * logRate e := by
    calc
      2 * B * F ≤ 2 * B * (802 * sqrtLogRate e) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = delta / 3 * logRate e := by
        rw [← sqrtLogRate_mul_sqrt he.le]
        dsimp [B, beta, q]
        ring
  refine ⟨hsprime, hsdvd, hssq, hmajor, hthree, hMlt, hcube, ?_, hrough⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hstride

end EKG.PartB
