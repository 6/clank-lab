import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked308 : stepCheck state308 step308 = true := by decide +kernel
theorem checked310 : stepCheck state310 step310 = true := by decide +kernel
theorem checked312 : stepCheck state312 step312 = true := by decide +kernel
theorem checked314 : stepCheck state314 step314 = true := by decide +kernel
theorem checked316 : stepCheck state316 step316 = true := by decide +kernel

theorem chunk35_checked : AllChecked state307 chunk35 :=
  ⟨(by rfl), ⟨checked308, ⟨(by rfl), ⟨checked310, ⟨(by rfl), ⟨checked312, ⟨(by rfl), ⟨checked314, ⟨(by rfl), ⟨checked316, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
