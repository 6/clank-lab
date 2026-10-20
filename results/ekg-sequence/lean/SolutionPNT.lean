import PrimeNumberTheoremAnd.Consequences

-- Exact epsilon estimate from the real-floor inclusive prime-count theorem.
-- The positive proof never imports a challenge specification.
theorem ekg_weak_pnt :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x| ≤
        ε * (x / Real.log x) := by
  intro ε hε
  have hbound := pi_alt'.isLittleO.def hε
  have hbound' : ∀ᶠ x : ℝ in Filter.atTop,
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x| ≤
        ε * |x / Real.log x| := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hbound
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hbound'
  refine ⟨max 2 Y, le_max_left _ _, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hnonneg : 0 ≤ x / Real.log x :=
    div_nonneg (by linarith) (Real.log_nonneg (by linarith))
  simpa only [abs_of_nonneg hnonneg] using hY x ((le_max_right _ _).trans hx)
