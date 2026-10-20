import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked234 : stepCheck state234 step234 = true := by decide +kernel
theorem checked236 : stepCheck state236 step236 = true := by decide +kernel
theorem checked238 : stepCheck state238 step238 = true := by decide +kernel
theorem checked240 : stepCheck state240 step240 = true := by decide +kernel
theorem checked242 : stepCheck state242 step242 = true := by decide +kernel

theorem chunk27_checked : AllChecked state233 chunk27 :=
  ⟨(by rfl), ⟨checked234, ⟨(by rfl), ⟨checked236, ⟨(by rfl), ⟨checked238, ⟨(by rfl), ⟨checked240, ⟨(by rfl), ⟨checked242, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
