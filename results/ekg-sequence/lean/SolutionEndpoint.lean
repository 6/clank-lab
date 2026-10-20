import EKG.EndpointTransfer
import SolutionCompatibilityPNT

-- The positive source imports only proved dependencies, never specifications.
-- Exactly the one-based, all-index, odd-prime-smoothed canonical endpoint.
theorem ekg_sharp_all_index :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |(EKG.CanonicalEndpoint.b n : ℝ) - (n : ℝ) -
        (n : ℝ) / (3 * Real.log (n : ℝ))| ≤
          ε * ((n : ℝ) / Real.log (n : ℝ)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (EKG.CanonicalEndpoint.canonical_endpoint_error_littleO.def hε)
  refine ⟨max 3 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by have := (le_max_left 3 N).trans hn; omega)
  have hb := hN n ((le_max_right _ _).trans hn)
  have heq : (n : ℝ)/(3*Real.log (n : ℝ)) = EKG.logRate (n : ℝ)/3 := by
    simp only [EKG.logRate, div_div, mul_comm]
  change |(EKG.CanonicalEndpoint.b n : ℝ) - (n : ℝ) -
      (n : ℝ)/(3*Real.log (n : ℝ))| ≤ ε*EKG.logRate (n : ℝ)
  rw [heq]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (EKG.logRate_nonneg hn1)] using hb

#print axioms ekg_sharp_all_index
