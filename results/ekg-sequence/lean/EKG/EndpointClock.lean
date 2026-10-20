import EKG.EndpointRemainders
import EKG.ClockRates
import SolutionCounting
import SolutionPNT
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace EKG.CanonicalEndpoint

open Real Filter Asymptotics
open scoped Topology

/-- The exact inclusive, real-floor PNT, with its proved epsilon endpoint
retained in the proof dependency closure. -/
theorem endpoint_realPrimeCount_equivalent :
    realPrimeCount ~[atTop] logRate := by
  change (fun x : ℝ => realPrimeCount x - logRate x) =o[atTop] logRate
  apply isLittleO_iff.mpr
  intro ε hε
  obtain ⟨X, hX, hbound⟩ := ekg_weak_pnt ε hε
  filter_upwards [eventually_ge_atTop X] with x hx
  have hx1 : 1 < x := by linarith
  change |realPrimeCount x - logRate x| ≤ ε * |logRate x|
  rw [abs_of_nonneg (logRate_nonneg hx1)]
  exact hbound x hx

/-- A fixed positive dilation changes the logarithm only by a constant. -/
theorem endpoint_log_div_equivalent (k : ℝ) (hk : 0 < k) :
    (fun x : ℝ => Real.log (x / k)) ~[atTop] Real.log := by
  have h := (IsEquivalent.refl : Real.log ~[atTop] Real.log).sub_isLittleO
    (Real.isLittleO_const_log_atTop (c := Real.log k))
  apply h.congr_left
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (Real.log_div hx.ne' hk.ne').symm

/-- Fixed-scale main terms, without replacing a natural quotient by an
uncontrolled rounded argument. -/
theorem endpoint_logRate_div_equivalent (k : ℝ) (hk : 0 < k) :
    (fun x : ℝ => logRate (x / k)) ~[atTop] (fun x => logRate x / k) := by
  have h := (IsEquivalent.refl : (fun x : ℝ => x / k) ~[atTop]
      (fun x : ℝ => x / k)).div (endpoint_log_div_equivalent k hk)
  convert! h using 1 <;> ext x <;> simp only [Pi.div_apply, logRate] <;> ring

/-- Each integer prime count at a fixed quotient has the required frontier
scale main term. The floor identity is exact, including the endpoints. -/
theorem endpoint_primeCounting_div (k : ℕ) (hk : 0 < k) :
    (fun t : ℕ => (Nat.primeCounting (frontier canonical t / k) : ℝ) -
      logRate (frontier canonical t : ℝ) / (k : ℝ)) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdiv : Tendsto (fun x : ℝ => x / (k : ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const hk'
  have hp := (endpoint_realPrimeCount_equivalent.comp_tendsto hdiv).trans
    (endpoint_logRate_div_equivalent (k : ℝ) hk')
  have hf : Tendsto (fun t : ℕ => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have hp' := (hp.comp_tendsto hf).isLittleO
  simp only [Function.comp_def, realPrimeCount, Nat.floor_div_eq_div, Nat.floor_natCast] at hp'
  have hp'' : (fun t : ℕ =>
      (Nat.primeCounting (frontier canonical t / k) : ℝ) -
        logRate (frontier canonical t : ℝ) / (k : ℝ)) =o[atTop]
      (fun t => (k : ℝ)⁻¹ * logRate (frontier canonical t : ℝ)) := by
    convert! hp' using 1 <;> ext t <;>
      simp only [Pi.sub_apply, div_eq_mul_inv, mul_comm]
  exact hp''.of_const_mul_right

/-- PNT supplies exactly the coefficient 1 - 2/2 + 1/3 = 1/3. -/
theorem canonical_prime_combination_littleO :
    (fun t : ℕ => (Nat.primeCounting (frontier canonical t) : ℝ) -
      2 * (Nat.primeCounting (frontier canonical t / 2) : ℝ) +
      (Nat.primeCounting (frontier canonical t / 3) : ℝ) -
      logRate (frontier canonical t : ℝ) / 3) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have h1 := endpoint_primeCounting_div 1 (by omega)
  have h2 := endpoint_primeCounting_div 2 (by omega)
  have h3 := endpoint_primeCounting_div 3 (by omega)
  have h := (h1.sub (h2.const_mul_left 2)).add h3
  apply h.congr_left
  intro t
  simp only [Pi.add_apply, Pi.sub_apply, Nat.div_one, Nat.cast_one, div_one,
    Nat.cast_ofNat]
  ring

/-- Exact finite counting plus negligible actual remainders yields the sharp
clock first in the frontier variable. -/
theorem canonical_frontier_clock_frontier_littleO :
    (fun t : ℕ => (frontier canonical t : ℝ) - ((t : ℝ) + 1) -
      logRate (frontier canonical t : ℝ) / 3) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have h := canonical_prime_combination_littleO.add canonical_counting_remainder_littleO
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with t ht
  have hc := (ekg_exact_counting t ht).2.2.2.2.2.2.2
  have hc' : (CanonicalCounting.e t : ℝ) - ((t + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (CanonicalCounting.e t) : ℝ) -
      2 * (Nat.primeCounting (CanonicalCounting.e t / 2) : ℝ) +
      (Nat.primeCounting (CanonicalCounting.e t / 3) : ℝ) +
      (CanonicalCounting.H t : ℝ) - (CanonicalCounting.K t : ℝ) -
      (CanonicalCounting.O t : ℝ) + (CanonicalCounting.correction t : ℝ) := by
    exact_mod_cast hc
  simp only [CanonicalCounting.e, Nat.cast_add, Nat.cast_one] at hc'
  linarith

/-- The old unconditional O-clock is used only to change variables; no
sharp estimate is assumed in this change. -/
theorem canonical_frontier_equivalent_time :
    (fun t : ℕ => (frontier canonical t : ℝ)) ~[atTop]
      (fun t => (t : ℝ) + 1) := by
  have hf : Tendsto (fun t : ℕ => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have h := (frontier_error_isBigO canonical).trans_isLittleO
    (logRate_isLittleO_self.comp_tendsto hf)
  have h' : (fun t : ℕ => (t : ℝ) + 1) ~[atTop]
      (fun t => (frontier canonical t : ℝ)) := by
    change (fun t : ℕ => ((t : ℝ) + 1) - (frontier canonical t : ℝ)) =o[atTop]
      (fun t => (frontier canonical t : ℝ))
    convert! h.neg_left using 1 <;> ext t <;>
      simp only [Function.comp_def, Pi.neg_apply, Nat.cast_add, Nat.cast_one, neg_sub]
  exact h'.symm

theorem canonical_frontier_logRate_equivalent_time :
    (fun t : ℕ => logRate (frontier canonical t : ℝ)) ~[atTop]
      (fun t => logRate ((t : ℝ) + 1)) := by
  have ht : Tendsto (fun t : ℕ => (t : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  convert! canonical_frontier_equivalent_time.div
    (canonical_frontier_equivalent_time.log ht) using 1 <;> rfl

/-- The canonical sharp frontier clock, with prefix length t+1 explicit. -/
theorem canonical_sharp_frontier_clock :
    (fun t : ℕ => (frontier canonical t : ℝ) - ((t : ℝ) + 1) -
      logRate ((t : ℝ) + 1) / 3) =o[atTop]
      (fun t => logRate ((t : ℝ) + 1)) := by
  have hclock := canonical_frontier_clock_frontier_littleO.trans_isBigO
    canonical_frontier_logRate_equivalent_time.isBigO
  have hchange := canonical_frontier_logRate_equivalent_time.isLittleO.const_mul_left
    (1 / 3 : ℝ)
  have h := hclock.add hchange
  apply h.congr_left
  intro t
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

end EKG.CanonicalEndpoint
