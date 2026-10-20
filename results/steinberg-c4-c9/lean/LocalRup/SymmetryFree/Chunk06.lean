import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked45 : stepCheck state45 step45 = true := by decide +kernel
theorem checked47 : stepCheck state47 step47 = true := by decide +kernel
theorem checked49 : stepCheck state49 step49 = true := by decide +kernel
theorem checked50 : stepCheck state50 step50 = true := by decide +kernel
theorem checked51 : stepCheck state51 step51 = true := by decide +kernel

theorem chunk6_checked : AllChecked state45 chunk6 :=
  ⟨checked45, ⟨(by rfl), ⟨checked47, ⟨(by rfl), ⟨checked49, ⟨checked50, ⟨checked51, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
