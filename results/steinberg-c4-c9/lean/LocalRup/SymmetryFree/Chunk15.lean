import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked126 : stepCheck state126 step126 = true := by decide +kernel
theorem checked128 : stepCheck state128 step128 = true := by decide +kernel
theorem checked130 : stepCheck state130 step130 = true := by decide +kernel
theorem checked131 : stepCheck state131 step131 = true := by decide +kernel
theorem checked133 : stepCheck state133 step133 = true := by decide +kernel

theorem chunk15_checked : AllChecked state126 chunk15 :=
  ⟨checked126, ⟨(by rfl), ⟨checked128, ⟨(by rfl), ⟨checked130, ⟨checked131, ⟨(by rfl), ⟨checked133, True.intro⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
