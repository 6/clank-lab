import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked60 : stepCheck state60 step60 = true := by decide +kernel
theorem checked62 : stepCheck state62 step62 = true := by decide +kernel
theorem checked64 : stepCheck state64 step64 = true := by decide +kernel
theorem checked66 : stepCheck state66 step66 = true := by decide +kernel
theorem checked68 : stepCheck state68 step68 = true := by decide +kernel

theorem chunk8_checked : AllChecked state59 chunk8 :=
  ⟨(by rfl), ⟨checked60, ⟨(by rfl), ⟨checked62, ⟨(by rfl), ⟨checked64, ⟨(by rfl), ⟨checked66, ⟨(by rfl), ⟨checked68, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
