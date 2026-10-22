/- Ported from root-parameter/project/N10Root/Root.lean (our earlier N10 root proof, Lean 4.33). -/
import ThomsonN10.Param.Calculus
import ThomsonN10.Param.BoxBounds

namespace ThomsonN10.Param
noncomputable section

theorem box_mem_coarse {h : ℝ} (hh : h ∈ Set.Icc left right) :
    h ∈ Set.Icc coarseLeft coarseRight :=
  ⟨box_inside_coarse.1.trans hh.1,hh.2.trans box_inside_coarse.2⟩

theorem box_energy_bound {h : ℝ} (hh : h ∈ Set.Icc left right) :
    energy h < 32717/1000 := coarse_energy_bound (box_mem_coarse hh)

theorem second_positive {h : ℝ} (hh : h ∈ Set.Icc left right) :
    0 < second h := coarse_second_positive (box_mem_coarse hh)

theorem first_continuousOn : ContinuousOn first (Set.Icc left right) := by
  intro h hh
  exact (first_hasDerivAt hh).continuousAt.continuousWithinAt

theorem first_strictMonoOn : StrictMonoOn first (Set.Icc left right) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc left right) first_continuousOn
  intro h hh
  have hh' : h ∈ Set.Icc left right := interior_subset hh
  rw [first_derivative hh']
  exact second_positive hh'

/-- Unique real stationary root in the exact authenticated final300-bit box. -/
theorem frozen_local_stationary_root :
    ∃! h : ℝ, h ∈ Set.Icc left right ∧ deriv energy h = 0 := by
  have hab := box_bounds.2.1.le
  have hz : (0 : ℝ) ∈ Set.Icc (first left) (first right) :=
    ⟨left_first_negative.le,right_first_positive.le⟩
  obtain ⟨h,hh,hzero⟩ := intermediate_value_Icc hab first_continuousOn hz
  refine ⟨h,⟨hh,?_⟩,?_⟩
  · rw [energy_derivative hh]
    exact hzero
  · intro g hg
    have hgzero : first g = 0 := by rw [← energy_derivative hg.1]; exact hg.2
    exact first_strictMonoOn.injOn hg.1 hh (hgzero.trans hzero.symm)

theorem frozen_local_stationary_root_interior :
    ∃! h : ℝ, h ∈ Set.Ioo left right ∧ deriv energy h = 0 := by
  obtain ⟨h,hh,hu⟩ := frozen_local_stationary_root
  have hz : first h = 0 := by rw [← energy_derivative hh.1]; exact hh.2
  have hl : left < h := lt_of_le_of_ne hh.1.1 (by
    intro heq
    have hx := left_first_negative
    rw [heq,hz] at hx
    exact (lt_irrefl (0 : ℝ)) hx)
  have hr : h < right := lt_of_le_of_ne hh.1.2 (by
    intro heq
    have hx := right_first_positive
    rw [← heq,hz] at hx
    exact (lt_irrefl (0 : ℝ)) hx)
  exact ⟨h,⟨⟨hl,hr⟩,hh.2⟩,fun g hg => hu g ⟨⟨hg.1.1.le,hg.1.2.le⟩,hg.2⟩⟩

/-- Exact handoff to a separately proved geometry/LP composition. -/
theorem root_energy_handoff :
    ∃! h : ℝ, h ∈ Set.Icc left right ∧ deriv energy h = 0 ∧
      h ∈ Set.Icc (42268742404398/100000000000000 : ℝ)
        (42268742404400/100000000000000 : ℝ) ∧ energy h < 32717/1000 := by
  obtain ⟨h,hh,hu⟩ := frozen_local_stationary_root
  refine ⟨h,⟨hh.1,hh.2,box_mem_coarse hh.1,box_energy_bound hh.1⟩,?_⟩
  intro g hg
  exact hu g ⟨hg.1,hg.2.1⟩
end
end ThomsonN10.Param
