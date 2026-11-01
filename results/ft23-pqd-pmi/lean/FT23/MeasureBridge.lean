import FT23.Definitions

noncomputable section
open Set MeasureTheory
namespace FT23

/-- Extension by zero through the subtype embedding gives the ambient necessary predicate. -/
theorem primaryPMI_implies_rectangleMeasure {F : ℝ → ℝ → ℝ}
    (h : PrimaryPMI F) : HasPositiveRectangleMeasure F := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ.map Subtype.val, ?_⟩
  intro a b d e habde
  have hm : MeasurableSet (rect a b d e) := measurableSet_Ioc.prod measurableSet_Ioc
  rw [Measure.map_apply measurable_subtype_coe hm]
  exact hμ a b d e habde

theorem rectangle_nonnegative {F : ℝ → ℝ → ℝ}
    (h : HasPositiveRectangleMeasure F) {a b d e : ℝ} (hr : ValidRect a b d e) :
    0 ≤ delta (E F) a b d e := by
  obtain ⟨μ, hμ⟩ := h
  obtain ⟨_, heq⟩ := hμ a b d e hr
  rw [← heq]
  exact ENNReal.toReal_nonneg

/-- The measure implication is proved before taking its contrapositive. -/
theorem negative_rectangle_not_PMI {F : ℝ → ℝ → ℝ} {a b d e : ℝ}
    (hr : ValidRect a b d e) (hn : delta (E F) a b d e < 0) : ¬ PrimaryPMI F := by
  intro hp
  exact (not_lt_of_ge (rectangle_nonnegative (primaryPMI_implies_rectangleMeasure hp) hr)) hn

end FT23
