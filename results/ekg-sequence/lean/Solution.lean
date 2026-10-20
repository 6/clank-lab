import EKG.PartA

theorem ekg_part_a :
    ∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
      max ((EKG.nonTickTop EKG.canonical u : ℝ) -
        (EKG.frontier EKG.canonical u : ℝ)) 0 ≤
        delta * (EKG.frontier EKG.canonical u : ℝ) /
          Real.log (EKG.frontier EKG.canonical u) :=
  EKG.PartA.canonical_upper_excursion
