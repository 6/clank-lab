import EKG.EndpointDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-- The exact one-based, all-index assertion; logarithms are natural. -/
def EndpointStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |(EKG.CanonicalEndpoint.b n : ℝ) - (n : ℝ) -
      (n : ℝ) / (3 * Real.log (n : ℝ))| ≤
        ε * ((n : ℝ) / Real.log (n : ℝ))
