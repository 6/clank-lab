import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked181 : stepCheck state181 step181 = true := by decide +kernel
theorem checked183 : stepCheck state183 step183 = true := by decide +kernel
theorem checked185 : stepCheck state185 step185 = true := by decide +kernel
theorem checked187 : stepCheck state187 step187 = true := by decide +kernel
theorem checked189 : stepCheck state189 step189 = true := by decide +kernel

theorem chunk21_checked : AllChecked state180 chunk21 :=
  ⟨(by rfl), ⟨checked181, ⟨(by rfl), ⟨checked183, ⟨(by rfl), ⟨checked185, ⟨(by rfl), ⟨checked187, ⟨(by rfl), ⟨checked189, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
