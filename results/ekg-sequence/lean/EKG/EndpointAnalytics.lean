import EKG.ClockRates
import EKG.RateAssembly
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace EKG.CanonicalEndpoint

open Real Filter Asymptotics
open scoped Topology

/-- The error scale diverges; bounded index shifts are negligible at this scale. -/
theorem endpoint_logRate_tendsto : Tendsto EKG.logRate atTop atTop := by
  obtain ⟨C, hC, hb⟩ := EKG.sqrt_isBigO_logRate.exists_pos
  apply tendsto_atTop_mono' atTop ?_
    (Real.tendsto_sqrt_atTop.atTop_div_const hC)
  filter_upwards [hb.bound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hb' : Real.sqrt x ≤ C * EKG.logRate x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      abs_of_nonneg (EKG.logRate_nonneg hx1)] using hx
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hb')

theorem endpoint_shift_time_equivalent (j : ℕ) :
    (fun n : ℕ => ((n - j : ℕ) : ℝ) + 1) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have h := (IsEquivalent.refl : (fun n : ℕ => (n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ))).add_const_of_norm_tendsto_atTop
      (c := 1 - (j : ℝ))
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  apply h.congr_left
  filter_upwards [eventually_ge_atTop j] with n hn
  simp only [Nat.cast_sub hn]
  ring

theorem endpoint_shift_logRate_equivalent (j : ℕ) :
    (fun n : ℕ => EKG.logRate (((n-j : ℕ) : ℝ) + 1)) ~[atTop]
      (fun n : ℕ => EKG.logRate (n : ℝ)) := by
  unfold EKG.logRate
  convert! (endpoint_shift_time_equivalent j).div
      ((endpoint_shift_time_equivalent j).log tendsto_natCast_atTop_atTop) using 1

/-- A finite shift of a proved expansion preserves its exact correction. -/
theorem endpoint_shift_expansion {F : ℕ → ℝ}
    (h : (fun t : ℕ => F t - ((t : ℝ)+1) - EKG.logRate ((t : ℝ)+1)/3)
      =o[atTop] (fun t => EKG.logRate ((t : ℝ)+1))) (j : ℕ) :
    (fun n : ℕ => F (n-j) - (n : ℝ) - EKG.logRate (n : ℝ)/3)
      =o[atTop] (fun n => EKG.logRate (n : ℝ)) := by
  have hc := (h.comp_tendsto (tendsto_sub_atTop_nat j)).trans_isBigO
    (endpoint_shift_logRate_equivalent j).isBigO
  have hconst : (fun _ : ℕ => (1 - (j : ℝ))) =o[atTop]
      (fun n : ℕ => EKG.logRate (n : ℝ)) :=
    isLittleO_const_left.mpr (Or.inr
      (tendsto_norm_atTop_atTop.comp
        (endpoint_logRate_tendsto.comp tendsto_natCast_atTop_atTop)))
  have htime : (fun n : ℕ => ((n-j : ℕ) : ℝ)+1-(n : ℝ)) =o[atTop]
      (fun n : ℕ => EKG.logRate (n : ℝ)) := by
    apply hconst.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop j] with n hn
    simp only [Nat.cast_sub hn]
    ring
  have hlog := (endpoint_shift_logRate_equivalent j).isLittleO.const_mul_left (1/3 : ℝ)
  have hs := (hc.add htime).add hlog
  apply hs.congr_left
  intro n
  simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply]
  ring

/-- The old, proved clock comparison suffices for this uniformly bounded
frontier-scale conversion; no sharp-clock hypothesis is used. -/
theorem endpoint_shift_frontier_scale :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 2 ≤ j → j ≤ 4 →
      EKG.logRate (frontier canonical (n-j) : ℝ) ≤
        4 * EKG.logRate (n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_frontier_comparable canonical)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 * Real.log 4))
  filter_upwards [eventually_ge_atTop (N+10), hlog] with n hn hln
  intro j hj2 hj4
  have hcomp := hN (n-j) (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlo : (n : ℝ) ≤ 2 * (((n-j : ℕ) : ℝ)+1) := by
    exact_mod_cast (show n ≤ 2*((n-j)+1) by omega)
  have hhi : ((n-j : ℕ) : ℝ)+1 ≤ (n : ℝ) := by
    exact_mod_cast (show n-j+1 ≤ n by omega)
  have hc1 : (((n-j : ℕ) : ℝ)+1)/2 ≤ (frontier canonical (n-j) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcomp.1
  have hc2 : (frontier canonical (n-j) : ℝ) ≤ 2*(((n-j : ℕ) : ℝ)+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcomp.2
  exact logRate_le_of_quarter_comparable hnpos (by linarith) (by linarith) hln

end EKG.CanonicalEndpoint
