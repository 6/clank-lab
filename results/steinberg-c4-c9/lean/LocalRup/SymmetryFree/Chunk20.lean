import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked171 : stepCheck state171 step171 = true := by decide +kernel
theorem checked173 : stepCheck state173 step173 = true := by decide +kernel
theorem checked175 : stepCheck state175 step175 = true := by decide +kernel
theorem checked177 : stepCheck state177 step177 = true := by decide +kernel
theorem checked179 : stepCheck state179 step179 = true := by decide +kernel

theorem chunk20_checked : AllChecked state170 chunk20 :=
  ⟨(by rfl), ⟨checked171, ⟨(by rfl), ⟨checked173, ⟨(by rfl), ⟨checked175, ⟨(by rfl), ⟨checked177, ⟨(by rfl), ⟨checked179, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
