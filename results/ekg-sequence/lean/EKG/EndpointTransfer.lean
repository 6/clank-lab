import EKG.EndpointAnalytics
import EKG.EndpointClock
import EKG.EndpointStructure

namespace EKG.CanonicalEndpoint

open Real Filter Asymptotics
open scoped Topology

/-- The three structural shifts have a single cutoff, hence this estimate
covers every sufficiently large index, including all prime blocks. -/
theorem canonical_endpoint_error_littleO :
    (fun n : ℕ => (b n : ℝ) - (n : ℝ) - EKG.logRate (n : ℝ)/3)
      =o[atTop] (fun n : ℕ => EKG.logRate (n : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨N, hN⟩ := eventual_frontier_proxy (ε/8) (by positivity)
  have h2 := (endpoint_shift_expansion canonical_sharp_frontier_clock 2).def (half_pos hε)
  have h3 := (endpoint_shift_expansion canonical_sharp_frontier_clock 3).def (half_pos hε)
  have h4 := (endpoint_shift_expansion canonical_sharp_frontier_clock 4).def (half_pos hε)
  filter_upwards [eventually_ge_atTop N, h2, h3, h4, endpoint_shift_frontier_scale,
    eventually_ge_atTop (3 : ℕ)] with n hn hc2 hc3 hc4 hscale hn3
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 ≤ EKG.logRate (n : ℝ) := EKG.logRate_nonneg hn1
  have hclock : ∀ j : ℕ, 2 ≤ j → j ≤ 4 →
      |(frontier canonical (n-j) : ℝ) - (n : ℝ) - EKG.logRate (n : ℝ)/3| ≤
        (ε/2) * EKG.logRate (n : ℝ) := by
    intro j hj2 hj4
    have hj : j=2 ∨ j=3 ∨ j=4 := by omega
    rcases hj with rfl | rfl | rfl
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hL] using hc2
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hL] using hc3
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hL] using hc4
  obtain ⟨j, hj2, hj4, hnear⟩ := hN n hn
  have hnear' : |(b n : ℝ) - (frontier canonical (n-j) : ℝ)| ≤
      (ε/8) * (4 * EKG.logRate (n : ℝ)) :=
    hnear.trans (mul_le_mul_of_nonneg_left (hscale j hj2 hj4) (by positivity))
  change |(b n : ℝ) - (n : ℝ) - EKG.logRate (n : ℝ)/3| ≤
    ε * |EKG.logRate (n : ℝ)|
  rw [abs_of_nonneg hL]
  calc
    _ = |((b n : ℝ)-(frontier canonical (n-j) : ℝ)) +
        ((frontier canonical (n-j) : ℝ)-(n : ℝ)-EKG.logRate (n : ℝ)/3)| := by
      congr 1
      ring
    _ ≤ |(b n : ℝ)-(frontier canonical (n-j) : ℝ)| +
        |(frontier canonical (n-j) : ℝ)-(n : ℝ)-EKG.logRate (n : ℝ)/3| := abs_add_le _ _
    _ ≤ (ε/8)*(4*EKG.logRate (n : ℝ)) + (ε/2)*EKG.logRate (n : ℝ) :=
      add_le_add hnear' (hclock j hj2 hj4)
    _ = ε*EKG.logRate (n : ℝ) := by ring

end EKG.CanonicalEndpoint
