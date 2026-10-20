import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked224 : stepCheck state224 step224 = true := by decide +kernel
theorem checked226 : stepCheck state226 step226 = true := by decide +kernel
theorem checked228 : stepCheck state228 step228 = true := by decide +kernel
theorem checked230 : stepCheck state230 step230 = true := by decide +kernel
theorem checked232 : stepCheck state232 step232 = true := by decide +kernel

theorem chunk26_checked : AllChecked state224 chunk26 :=
  ⟨checked224, ⟨(by rfl), ⟨checked226, ⟨(by rfl), ⟨checked228, ⟨(by rfl), ⟨checked230, ⟨(by rfl), ⟨checked232, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
