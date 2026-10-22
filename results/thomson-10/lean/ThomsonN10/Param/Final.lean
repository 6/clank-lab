import ThomsonN10.Interfaces
import ThomsonN10.Param.Root

/-! P0: ParameterExistsUnique, from the ported exact-box root proof. -/

namespace ThomsonN10.Param

theorem left_eq : left = (heightLower : ℝ) := by
  unfold left heightLower; push_cast; rfl

theorem right_eq : right = (heightUpper : ℝ) := by
  unfold right heightUpper; push_cast; rfl

theorem first_eq (h : ℝ) : first h = ThomsonN10.stationarity h := by
  unfold first ThomsonN10.stationarity z dc dd capMinus capPlus r
  rfl

theorem ParameterExistsUnique_holds : ThomsonN10.Interfaces.ParameterExistsUnique := by
  have hab := box_bounds.2.1.le
  have hz : (0 : ℝ) ∈ Set.Icc (first left) (first right) :=
    ⟨left_first_negative.le, right_first_positive.le⟩
  obtain ⟨h, hh, hzero⟩ := intermediate_value_Icc hab first_continuousOn hz
  rw [left_eq, right_eq] at hh
  refine ⟨h, ⟨hh.1, hh.2, ?_⟩, ?_⟩
  · rw [← first_eq]; exact hzero
  · rintro g ⟨g1, g2, g3⟩
    rw [← left_eq] at g1
    rw [← right_eq] at g2
    rw [← first_eq] at g3
    rw [← left_eq, ← right_eq] at hh
    exact first_strictMonoOn.injOn ⟨g1, g2⟩ hh (g3.trans hzero.symm)

end ThomsonN10.Param

#print axioms ThomsonN10.Param.ParameterExistsUnique_holds
