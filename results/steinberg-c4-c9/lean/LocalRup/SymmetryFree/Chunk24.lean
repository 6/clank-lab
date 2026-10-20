import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked206 : stepCheck state206 step206 = true := by decide +kernel
theorem checked208 : stepCheck state208 step208 = true := by decide +kernel
theorem checked210 : stepCheck state210 step210 = true := by decide +kernel
theorem checked212 : stepCheck state212 step212 = true := by decide +kernel
theorem checked214 : stepCheck state214 step214 = true := by decide +kernel

theorem chunk24_checked : AllChecked state205 chunk24 :=
  ⟨(by rfl), ⟨checked206, ⟨(by rfl), ⟨checked208, ⟨(by rfl), ⟨checked210, ⟨(by rfl), ⟨checked212, ⟨(by rfl), ⟨checked214, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
