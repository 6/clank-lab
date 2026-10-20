import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked270 : stepCheck state270 step270 = true := by decide +kernel
theorem checked272 : stepCheck state272 step272 = true := by decide +kernel
theorem checked274 : stepCheck state274 step274 = true := by decide +kernel
theorem checked276 : stepCheck state276 step276 = true := by decide +kernel
theorem checked278 : stepCheck state278 step278 = true := by decide +kernel

theorem chunk31_checked : AllChecked state269 chunk31 :=
  ⟨(by rfl), ⟨checked270, ⟨(by rfl), ⟨checked272, ⟨(by rfl), ⟨checked274, ⟨(by rfl), ⟨checked276, ⟨(by rfl), ⟨checked278, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
