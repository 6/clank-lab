import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked135 : stepCheck state135 step135 = true := by decide +kernel
theorem checked137 : stepCheck state137 step137 = true := by decide +kernel
theorem checked139 : stepCheck state139 step139 = true := by decide +kernel
theorem checked140 : stepCheck state140 step140 = true := by decide +kernel
theorem checked141 : stepCheck state141 step141 = true := by decide +kernel

theorem chunk16_checked : AllChecked state134 chunk16 :=
  ⟨(by rfl), ⟨checked135, ⟨(by rfl), ⟨checked137, ⟨(by rfl), ⟨checked139, ⟨checked140, ⟨checked141, True.intro⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
