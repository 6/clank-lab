import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked29 : stepCheck state29 step29 = true := by decide +kernel
theorem checked31 : stepCheck state31 step31 = true := by decide +kernel
theorem checked33 : stepCheck state33 step33 = true := by decide +kernel
theorem checked35 : stepCheck state35 step35 = true := by decide +kernel
theorem checked37 : stepCheck state37 step37 = true := by decide +kernel

theorem chunk4_checked : AllChecked state28 chunk4 :=
  ⟨(by rfl), ⟨checked29, ⟨(by rfl), ⟨checked31, ⟨(by rfl), ⟨checked33, ⟨(by rfl), ⟨checked35, ⟨(by rfl), ⟨checked37, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
