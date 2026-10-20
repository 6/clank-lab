import EKG.PrimeEstimates

/-! Analytic rate conversions for the EKG manuscript. The scalar span
lemma records its actual quantitative hypotheses. No sequence rate is
assumed or asserted here. -/
namespace EKG

open Real Filter Asymptotics
open scoped Topology

theorem logSqRate_le_logRate {x : ℝ} (hx : 0 ≤ x) (hl : 1 ≤ Real.log x) :
    logSqRate x ≤ logRate x := by
  unfold logSqRate logRate
  apply div_le_div_of_nonneg_left hx (by linarith)
  nlinarith

theorem sqrtLogRate_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    sqrtLogRate x * Real.sqrt x = logRate x := by
  unfold sqrtLogRate logRate
  rw [div_mul_eq_mul_div, Real.mul_self_sqrt hx]

/-- Converts the quadratic span from manuscript Theorem 1(b) into a
linear logarithmic rate, with an explicit constant. -/
theorem span_bound_of_count_bound {x k D : ℝ}
    (hx : 0 ≤ x) (hk : 0 ≤ k) (hD : 0 ≤ D)
    (hl : 1 ≤ Real.log x) (hcount : k ≤ D * sqrtLogRate x) :
    2 * k ^ 2 + 2 * k * Real.sqrt (k ^ 2 + x) ≤
      (4 * D ^ 2 + 2 * D) * logRate x := by
  have hs : Real.sqrt (k ^ 2 + x) ≤ k + Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x,
        mul_nonneg hk (Real.sqrt_nonneg x)]
  have hr : 0 ≤ sqrtLogRate x := by
    unfold sqrtLogRate
    exact div_nonneg (Real.sqrt_nonneg x) (by linarith)
  have hk2 : k ^ 2 ≤ D ^ 2 * sqrtLogRate x ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ hk (mul_nonneg hD hr)).mpr hcount
  have hmul : k * Real.sqrt x ≤ D * logRate x := by
    calc
      _ ≤ (D * sqrtLogRate x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hcount (Real.sqrt_nonneg x)
      _ = _ := by rw [mul_assoc, sqrtLogRate_mul_sqrt hx]
  have hsq : k ^ 2 ≤ D ^ 2 * logRate x := by
    calc
      _ ≤ D ^ 2 * logSqRate x := by simpa [sqrtLogRate_sq hx] using hk2
      _ ≤ _ := mul_le_mul_of_nonneg_left (logSqRate_le_logRate hx hl) (sq_nonneg D)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * k by positivity)
  nlinarith

theorem eventually_bootstrap_count_bound : ∀ᶠ x : ℝ in atTop,
    12 * sqrtPrimeCount x + 721 ≤ 793 * sqrtLogRate x := by
  filter_upwards [eventually_sqrtPrimeCount_le, eventually_one_le_sqrtLogRate]
    with x hp hr
  linarith

noncomputable def spanMajorant (x : ℝ) : ℝ :=
  let k := 12 * sqrtPrimeCount x + 721
  2 * k ^ 2 + 2 * k * Real.sqrt (k ^ 2 + x)

theorem eventually_spanMajorant_le : ∀ᶠ x : ℝ in atTop,
    spanMajorant x ≤ (4 * 793 ^ 2 + 2 * 793 : ℝ) * logRate x := by
  filter_upwards [eventually_bootstrap_count_bound,
    eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hk hx hl
  apply span_bound_of_count_bound hx ?_ (by norm_num) hl hk
  unfold sqrtPrimeCount realPrimeCount
  positivity

theorem spanMajorant_isBigO : spanMajorant =O[atTop] logRate := by
  apply IsBigO.of_bound (4 * 793 ^ 2 + 2 * 793)
  filter_upwards [eventually_spanMajorant_le, eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  have hs : 0 ≤ spanMajorant x := by
    unfold spanMajorant sqrtPrimeCount realPrimeCount
    positivity
  have hr : 0 ≤ logRate x := logRate_nonneg hx1
  simpa only [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg hr] using hx

theorem logRate_isLittleO_self : logRate =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto'
    (Filter.Eventually.of_forall (fun x hx => by simp [logRate, hx]))).mpr
  apply Tendsto.congr' (f₁ := fun x : ℝ => (Real.log x)⁻¹) ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hn : x ≠ 0 := by linarith
  unfold logRate
  field_simp [hn]

theorem logSqRate_isLittleO_logRate : logSqRate =o[atTop] logRate := by
  apply (isLittleO_iff_tendsto' (by simp [logSqRate, logRate])).mpr
  apply Tendsto.congr' (f₁ := fun x : ℝ => (Real.log x)⁻¹) ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hn : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  unfold logSqRate logRate
  field_simp [hn, hl]

theorem sqrtLogRate_isLittleO_logRate : sqrtLogRate =o[atTop] logRate := by
  have hzero : ∀ᶠ x : ℝ in atTop, logRate x = 0 → sqrtLogRate x = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hn : logRate x ≠ 0 :=
      div_ne_zero (by linarith) (ne_of_gt (Real.log_pos hx))
    exact fun h => False.elim (hn h)
  apply (isLittleO_iff_tendsto' hzero).mpr
  apply Tendsto.congr' (f₁ := fun x : ℝ => (Real.sqrt x)⁻¹) ?_
    Real.tendsto_sqrt_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hs := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hn : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  unfold sqrtLogRate logRate
  field_simp [hn, hl, hx0]
  nlinarith

theorem sqrtPrimeCount_isLittleO_logRate : sqrtPrimeCount =o[atTop] logRate :=
  sqrtPrimeCount_isBigO.trans_isLittleO sqrtLogRate_isLittleO_logRate

theorem primeCounting_nat_isBigO :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) =O[atTop]
      (fun n : ℕ => logRate (n : ℝ)) := by
  simpa [Function.comp_def, realPrimeCount] using
    realPrimeCount_isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem primeCounting_sqrt_nat_isBigO :
    (fun n : ℕ => (Nat.primeCounting (Nat.sqrt n) : ℝ)) =O[atTop]
      (fun n : ℕ => sqrtLogRate (n : ℝ)) := by
  simpa [Function.comp_def, sqrtPrimeCount, realPrimeCount] using
    sqrtPrimeCount_isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem primeCounting_sqrt_nat_isLittleO_logRate :
    (fun n : ℕ => (Nat.primeCounting (Nat.sqrt n) : ℝ)) =o[atTop]
      (fun n : ℕ => logRate (n : ℝ)) := by
  simpa [Function.comp_def, sqrtPrimeCount, realPrimeCount] using
    sqrtPrimeCount_isLittleO_logRate.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem holes_majorant_isLittleO_logRate :
    (fun x => sqrtPrimeCount x * (13 * sqrtPrimeCount x + 725))
      =o[atTop] logRate :=
  holes_majorant_isBigO.trans_isLittleO logSqRate_isLittleO_logRate

theorem holes_majorant_nat_isBigO :
    (fun n : ℕ => ((Nat.primeCounting (Nat.sqrt n) *
      (13 * Nat.primeCounting (Nat.sqrt n) + 725) : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => logSqRate (n : ℝ)) := by
  simpa [Function.comp_def, sqrtPrimeCount, realPrimeCount] using
    holes_majorant_isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- Rate comparison for changing the frontier variable to the time variable. -/
theorem logRate_le_of_comparable {e t : ℝ} (ht : 0 < t)
    (he : t / 2 ≤ e) (he' : e ≤ 2 * t)
    (hl : 2 * Real.log 2 ≤ Real.log t) : logRate e ≤ 4 * logRate t := by
  have he0 : 0 < e := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : 0 < Real.log t := by linarith
  have hle : Real.log t / 2 ≤ Real.log e := by
    have h := Real.log_le_log (show 0 < t / 2 by positivity) he
    rw [Real.log_div (ne_of_gt ht) (by norm_num)] at h
    linarith
  unfold logRate
  calc
    _ ≤ (2 * t) / Real.log e :=
      div_le_div_of_nonneg_right he' (by linarith)
    _ ≤ (2 * t) / (Real.log t / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hle
    _ = 4 * (t / Real.log t) := by ring

/-- Absorbs an error stated in terms of `e` before changing variables. -/
theorem comparable_of_logRate_error {e t C : ℝ}
    (he : 0 < e) (hl : 0 < Real.log e)
    (hlarge : 2 * C ≤ Real.log e)
    (herr : |e - t| ≤ C * logRate e) : t / 2 ≤ e ∧ e ≤ 2 * t := by
  have hhalf : C * logRate e ≤ e / 2 := by
    unfold logRate
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    nlinarith
  have ha := abs_le.mp (herr.trans hhalf)
  constructor <;> linarith

/-- Transfer lemma for errors with a frontier scale, assuming the two
quantitative comparisons that the combinatorics must establish. -/
theorem logRate_comp_isBigO {ι : Type*} {l : Filter ι} {e t : ι → ℝ}
    (ht : Tendsto t l atTop)
    (he : ∀ᶠ i in l, t i / 2 ≤ e i ∧ e i ≤ 2 * t i) :
    (fun i => logRate (e i)) =O[l] (fun i => logRate (t i)) := by
  apply IsBigO.of_bound 4
  filter_upwards [he, ht.eventually (eventually_gt_atTop (0 : ℝ)),
    (Real.tendsto_log_atTop.comp ht).eventually
      (eventually_ge_atTop (2 * Real.log 2))] with i hi hit hil
  change 2 * Real.log 2 ≤ Real.log (t i) at hil
  have hib := logRate_le_of_comparable hit hi.1 hi.2 hil
  have het : 0 < e i := by linarith [hi.1]
  have hlogt : 0 < Real.log (t i) := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hloge : 0 < Real.log (e i) := by
    have h := Real.log_le_log (show 0 < t i / 2 by positivity) hi.1
    rw [Real.log_div (ne_of_gt hit) (by norm_num)] at h
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hp : 0 ≤ logRate (e i) := by unfold logRate; positivity
  have hq : 0 ≤ logRate (t i) := by unfold logRate; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq] using hib

theorem eventually_comparable_of_logRate_error {ι : Type*} {l : Filter ι}
    {e t : ι → ℝ} (he : Tendsto e l atTop)
    (herr : (fun i => e i - t i) =O[l] (fun i => logRate (e i))) :
    ∀ᶠ i in l, t i / 2 ≤ e i ∧ e i ≤ 2 * t i := by
  obtain ⟨C, _, hb⟩ := herr.exists_nonneg
  filter_upwards [hb.bound, he.eventually (eventually_gt_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp he).eventually
      (eventually_ge_atTop (2 * C))] with i hi hei hli
  have hi' : |e i - t i| ≤ C * logRate (e i) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (logRate_nonneg hei)] using hi
  exact comparable_of_logRate_error (by linarith) (Real.log_pos hei) hli hi'

/-- The final change of variables needs only the already established
error `e-t = O(e/log e)` and divergence of the frontier. -/
theorem logRate_error_transfer {ι : Type*} {l : Filter ι} {e t : ι → ℝ}
    (he : Tendsto e l atTop)
    (herr : (fun i => e i - t i) =O[l] (fun i => logRate (e i))) :
    Tendsto t l atTop ∧
      (fun i => e i - t i) =O[l] (fun i => logRate (t i)) := by
  have hc := eventually_comparable_of_logRate_error he herr
  have ht : Tendsto t l atTop := by
    apply tendsto_atTop_mono' l ?_ (he.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
    filter_upwards [hc] with i hi
    linarith [hi.2]
  exact ⟨ht, herr.trans (logRate_comp_isBigO ht hc)⟩

theorem sqrtPrimeCount_mul_sqrt_isBigO :
    (fun x => sqrtPrimeCount x * Real.sqrt x) =O[atTop] logRate := by
  have h := sqrtPrimeCount_isBigO.mul (isBigO_refl Real.sqrt atTop)
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact sqrtLogRate_mul_sqrt hx

theorem sqrt_isBigO_logRate : Real.sqrt =O[atTop] logRate := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_one_le_sqrtLogRate, eventually_gt_atTop (1 : ℝ)]
    with x hr hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hls : Real.log x ≤ Real.sqrt x := by
    have h := (le_div_iff₀ hl).mp hr
    simpa only [one_mul] using h
  have hs := mul_le_mul_of_nonneg_right hls (Real.sqrt_nonneg x)
  have h : Real.sqrt x ≤ logRate x := by
    unfold logRate
    apply (le_div_iff₀ hl).mpr
    nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (logRate_nonneg hx), one_mul] using h

noncomputable def positionHoleMajorant (x : ℝ) : ℝ :=
  2 * Real.sqrt x * (13 * sqrtPrimeCount x + 724)

theorem positionHoleMajorant_isBigO : positionHoleMajorant =O[atTop] logRate := by
  have h := (sqrtPrimeCount_mul_sqrt_isBigO.const_mul_left 26).add
    (sqrt_isBigO_logRate.const_mul_left 1448)
  apply h.congr_left
  intro x
  unfold positionHoleMajorant
  ring

theorem eventually_positionHoleMajorant_le : ∀ᶠ x : ℝ in atTop,
    positionHoleMajorant x ≤ 1604 * logRate x := by
  filter_upwards [eventually_sqrtPrimeCount_le, eventually_one_le_sqrtLogRate,
    eventually_ge_atTop (0 : ℝ)] with x hp hr hx
  unfold positionHoleMajorant
  calc
    _ ≤ 2 * Real.sqrt x * (802 * sqrtLogRate x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1604 * logRate x := by
      rw [← sqrtLogRate_mul_sqrt hx]
      ring

theorem positionHoleMajorant_nat_le (n : ℕ) :
    ((2 * Nat.sqrt n * (13 * Nat.primeCounting (Nat.sqrt n) + 724) : ℕ) : ℝ)
      ≤ positionHoleMajorant (n : ℝ) := by
  push_cast
  rw [primeCounting_sqrt_nat_eq]
  unfold positionHoleMajorant
  apply mul_le_mul_of_nonneg_right ?_ (by
    unfold sqrtPrimeCount realPrimeCount; positivity)
  exact mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num)

theorem positionHoleMajorant_nat_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((2 * Nat.sqrt n * (13 * Nat.primeCounting (Nat.sqrt n) + 724) : ℕ) : ℝ)
      ≤ 1604 * (n : ℝ) / Real.log (n : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      eventually_positionHoleMajorant_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun n hn => (positionHoleMajorant_nat_le n).trans ?_⟩
  simpa only [logRate, mul_div_assoc] using hN n hn

theorem sqrtPrimeCount_mul_sqrt_nat_isBigO :
    (fun n : ℕ => (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.sqrt (n : ℝ))
      =O[atTop] (fun n : ℕ => logRate (n : ℝ)) := by
  simpa [Function.comp_def, sqrtPrimeCount, realPrimeCount] using
    sqrtPrimeCount_mul_sqrt_isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem positionHoleMajorant_nat_isBigO :
    (fun n : ℕ => ((2 * Nat.sqrt n *
      (13 * Nat.primeCounting (Nat.sqrt n) + 724) : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ => logRate (n : ℝ)) := by
  apply IsBigO.of_bound 1604
  obtain ⟨N, hN⟩ := positionHoleMajorant_nat_bound
  filter_upwards [eventually_ge_atTop N,
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn1
  have hnonneg : 0 ≤ ((2 * Nat.sqrt n *
      (13 * Nat.primeCounting (Nat.sqrt n) + 724) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (logRate_nonneg hn1)]
  simpa only [logRate, mul_div_assoc] using hN n hn

end EKG
