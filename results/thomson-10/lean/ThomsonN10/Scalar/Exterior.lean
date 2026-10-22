/- Adapted from proof/lean/ThomsonN9/Bernstein/Minorant.lean and
   proof/lean/ClaudeL2b/RefinedWindows.lean,
   aravindkarthigeyan/thomson-n9-lean, MIT, commit
   168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Scalar.ExteriorBounds
import ThomsonN10.Scalar.Contacts
namespace ThomsonN10.Scalar

theorem ExteriorGap_holds : ThomsonN10.Interfaces.ExteriorGap := by
  intro h t ht1 ht2 hw
  have side : ∀ j : Fin 7,
      t ≤ contact h (contactOrder j) - (windowRadius : ℝ) ∨
      contact h (contactOrder j) + (windowRadius : ℝ) ≤ t := by
    intro j
    rcases le_abs'.1 (hw (contactOrder j)) with ha | ha
    · left; linarith
    · right; linarith
  obtain ⟨lo0, hi0⟩ := contact_bounds h 0
  obtain ⟨lo1, hi1⟩ := contact_bounds h 1
  obtain ⟨lo2, hi2⟩ := contact_bounds h 2
  obtain ⟨lo3, hi3⟩ := contact_bounds h 3
  obtain ⟨lo4, hi4⟩ := contact_bounds h 4
  obtain ⟨lo5, hi5⟩ := contact_bounds h 5
  obtain ⟨lo6, hi6⟩ := contact_bounds h 6
  rcases side 0 with c0 | c0
  · norm_num [contact, contactOrder, windowRadius] at c0
    linarith
  rcases side 1 with c1 | c1
  · apply exterior_bound1
    · norm_num [exteriorLo1, contactLo, windowRadius, contactOrder] at lo0 c0 ⊢
      linarith
    · norm_num [exteriorHi1, contactHi, windowRadius, contactOrder] at hi1 c1 ⊢
      linarith
  rcases side 2 with c2 | c2
  · apply exterior_bound2
    · norm_num [exteriorLo2, contactLo, windowRadius, contactOrder] at lo1 c1 ⊢
      linarith
    · norm_num [exteriorHi2, contactHi, windowRadius, contactOrder] at hi2 c2 ⊢
      linarith
  rcases side 3 with c3 | c3
  · apply exterior_bound3
    · norm_num [exteriorLo3, contactLo, windowRadius, contactOrder] at lo2 c2 ⊢
      linarith
    · norm_num [exteriorHi3, contactHi, windowRadius, contactOrder] at hi3 c3 ⊢
      linarith
  rcases side 4 with c4 | c4
  · apply exterior_bound4
    · norm_num [exteriorLo4, contactLo, windowRadius, contactOrder] at lo3 c3 ⊢
      linarith
    · norm_num [exteriorHi4, contactHi, windowRadius, contactOrder] at hi4 c4 ⊢
      linarith
  rcases side 5 with c5 | c5
  · apply exterior_bound5
    · norm_num [exteriorLo5, contactLo, windowRadius, contactOrder] at lo4 c4 ⊢
      linarith
    · norm_num [exteriorHi5, contactHi, windowRadius, contactOrder] at hi5 c5 ⊢
      linarith
  rcases side 6 with c6 | c6
  · apply exterior_bound6
    · norm_num [exteriorLo6, contactLo, windowRadius, contactOrder] at lo5 c5 ⊢
      linarith
    · norm_num [exteriorHi6, contactHi, windowRadius, contactOrder] at hi6 c6 ⊢
      linarith
  apply exterior_bound7
  · norm_num [exteriorLo7, contactLo, windowRadius, contactOrder] at lo6 c6 ⊢
    linarith
  · simpa [exteriorHi7, pairCap] using ht2
end ThomsonN10.Scalar
#print axioms ThomsonN10.Scalar.ExteriorGap_holds
