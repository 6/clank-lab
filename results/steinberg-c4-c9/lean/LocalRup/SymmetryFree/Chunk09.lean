import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked70 : stepCheck state70 step70 = true := by decide +kernel
theorem checked72 : stepCheck state72 step72 = true := by decide +kernel
theorem checked74 : stepCheck state74 step74 = true := by decide +kernel
theorem checked76 : stepCheck state76 step76 = true := by decide +kernel
theorem checked78 : stepCheck state78 step78 = true := by decide +kernel

theorem chunk9_checked : AllChecked state69 chunk9 :=
  ⟨(by rfl), ⟨checked70, ⟨(by rfl), ⟨checked72, ⟨(by rfl), ⟨checked74, ⟨(by rfl), ⟨checked76, ⟨(by rfl), ⟨checked78, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
