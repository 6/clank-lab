import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked280 : stepCheck state280 step280 = true := by decide +kernel
theorem checked282 : stepCheck state282 step282 = true := by decide +kernel
theorem checked284 : stepCheck state284 step284 = true := by decide +kernel
theorem checked286 : stepCheck state286 step286 = true := by decide +kernel
theorem checked288 : stepCheck state288 step288 = true := by decide +kernel

theorem chunk32_checked : AllChecked state279 chunk32 :=
  ⟨(by rfl), ⟨checked280, ⟨(by rfl), ⟨checked282, ⟨(by rfl), ⟨checked284, ⟨(by rfl), ⟨checked286, ⟨(by rfl), ⟨checked288, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
