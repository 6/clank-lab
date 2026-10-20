import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked260 : stepCheck state260 step260 = true := by decide +kernel
theorem checked262 : stepCheck state262 step262 = true := by decide +kernel
theorem checked264 : stepCheck state264 step264 = true := by decide +kernel
theorem checked266 : stepCheck state266 step266 = true := by decide +kernel
theorem checked268 : stepCheck state268 step268 = true := by decide +kernel

theorem chunk30_checked : AllChecked state259 chunk30 :=
  ⟨(by rfl), ⟨checked260, ⟨(by rfl), ⟨checked262, ⟨(by rfl), ⟨checked264, ⟨(by rfl), ⟨checked266, ⟨(by rfl), ⟨checked268, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
