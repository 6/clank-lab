import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked109 : stepCheck state109 step109 = true := by decide +kernel
theorem checked111 : stepCheck state111 step111 = true := by decide +kernel
theorem checked113 : stepCheck state113 step113 = true := by decide +kernel
theorem checked115 : stepCheck state115 step115 = true := by decide +kernel
theorem checked117 : stepCheck state117 step117 = true := by decide +kernel

theorem chunk13_checked : AllChecked state108 chunk13 :=
  ⟨(by rfl), ⟨checked109, ⟨(by rfl), ⟨checked111, ⟨(by rfl), ⟨checked113, ⟨(by rfl), ⟨checked115, ⟨(by rfl), ⟨checked117, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
