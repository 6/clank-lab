import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked328 : stepCheck state328 step328 = true := by decide +kernel
theorem checked330 : stepCheck state330 step330 = true := by decide +kernel
theorem checked332 : stepCheck state332 step332 = true := by decide +kernel
theorem checked334 : stepCheck state334 step334 = true := by decide +kernel
theorem checked336 : stepCheck state336 step336 = true := by decide +kernel

theorem chunk37_checked : AllChecked state327 chunk37 :=
  ⟨(by rfl), ⟨checked328, ⟨(by rfl), ⟨checked330, ⟨(by rfl), ⟨checked332, ⟨(by rfl), ⟨checked334, ⟨(by rfl), ⟨checked336, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
