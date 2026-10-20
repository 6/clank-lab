import EKG.PartB

theorem ekg_part_b :
    ∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
      ∀ h : ℕ, 2 ≤ h → ¬ h.Prime → h < EKG.frontier EKG.canonical u →
        ¬ EKG.UsedBefore EKG.canonical.a (u + 1) h →
        (EKG.frontier EKG.canonical u : ℝ) - (h : ℝ) <
          delta * (EKG.frontier EKG.canonical u : ℝ) /
            Real.log (EKG.frontier EKG.canonical u) :=
  EKG.PartB.canonical_missing_composite
