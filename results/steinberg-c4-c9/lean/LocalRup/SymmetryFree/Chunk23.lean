import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked197 : stepCheck state197 step197 = true := by decide +kernel
theorem checked198 : stepCheck state198 step198 = true := by decide +kernel
theorem checked200 : stepCheck state200 step200 = true := by decide +kernel
theorem checked202 : stepCheck state202 step202 = true := by decide +kernel
theorem checked204 : stepCheck state204 step204 = true := by decide +kernel

theorem chunk23_checked : AllChecked state196 chunk23 :=
  ⟨(by rfl), ⟨checked197, ⟨checked198, ⟨(by rfl), ⟨checked200, ⟨(by rfl), ⟨checked202, ⟨(by rfl), ⟨checked204, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
