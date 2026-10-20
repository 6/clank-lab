import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked290 : stepCheck state290 step290 = true := by decide +kernel
theorem checked292 : stepCheck state292 step292 = true := by decide +kernel
theorem checked294 : stepCheck state294 step294 = true := by decide +kernel
theorem checked296 : stepCheck state296 step296 = true := by decide +kernel
theorem checked297 : stepCheck state297 step297 = true := by decide +kernel

theorem chunk33_checked : AllChecked state289 chunk33 :=
  ⟨(by rfl), ⟨checked290, ⟨(by rfl), ⟨checked292, ⟨(by rfl), ⟨checked294, ⟨(by rfl), ⟨checked296, ⟨checked297, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
