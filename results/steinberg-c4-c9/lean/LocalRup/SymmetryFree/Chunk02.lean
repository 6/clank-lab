import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked15 : stepCheck state15 step15 = true := by decide +kernel
theorem checked16 : stepCheck state16 step16 = true := by decide +kernel
theorem checked18 : stepCheck state18 step18 = true := by decide +kernel
theorem checked19 : stepCheck state19 step19 = true := by decide +kernel
theorem checked20 : stepCheck state20 step20 = true := by decide +kernel

theorem chunk2_checked : AllChecked state14 chunk2 :=
  ⟨(by rfl), ⟨checked15, ⟨checked16, ⟨(by rfl), ⟨checked18, ⟨checked19, ⟨checked20, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
