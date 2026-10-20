import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked7 : stepCheck state7 step7 = true := by decide +kernel
theorem checked8 : stepCheck state8 step8 = true := by decide +kernel
theorem checked10 : stepCheck state10 step10 = true := by decide +kernel
theorem checked12 : stepCheck state12 step12 = true := by decide +kernel
theorem checked13 : stepCheck state13 step13 = true := by decide +kernel

theorem chunk1_checked : AllChecked state7 chunk1 :=
  ⟨checked7, ⟨checked8, ⟨(by rfl), ⟨checked10, ⟨(by rfl), ⟨checked12, ⟨checked13, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
