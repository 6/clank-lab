import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked1 : stepCheck state1 step1 = true := by decide +kernel
theorem checked2 : stepCheck state2 step2 = true := by decide +kernel
theorem checked3 : stepCheck state3 step3 = true := by decide +kernel
theorem checked4 : stepCheck state4 step4 = true := by decide +kernel
theorem checked6 : stepCheck state6 step6 = true := by decide +kernel

theorem chunk0_checked : AllChecked state0 chunk0 :=
  ⟨(by rfl), ⟨checked1, ⟨checked2, ⟨checked3, ⟨checked4, ⟨(by rfl), ⟨checked6, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
