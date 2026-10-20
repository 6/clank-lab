import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked162 : stepCheck state162 step162 = true := by decide +kernel
theorem checked164 : stepCheck state164 step164 = true := by decide +kernel
theorem checked166 : stepCheck state166 step166 = true := by decide +kernel
theorem checked168 : stepCheck state168 step168 = true := by decide +kernel
theorem checked169 : stepCheck state169 step169 = true := by decide +kernel

theorem chunk19_checked : AllChecked state161 chunk19 :=
  ⟨(by rfl), ⟨checked162, ⟨(by rfl), ⟨checked164, ⟨(by rfl), ⟨checked166, ⟨(by rfl), ⟨checked168, ⟨checked169, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
