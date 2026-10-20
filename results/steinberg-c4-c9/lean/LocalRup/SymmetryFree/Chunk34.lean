import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked299 : stepCheck state299 step299 = true := by decide +kernel
theorem checked300 : stepCheck state300 step300 = true := by decide +kernel
theorem checked302 : stepCheck state302 step302 = true := by decide +kernel
theorem checked304 : stepCheck state304 step304 = true := by decide +kernel
theorem checked306 : stepCheck state306 step306 = true := by decide +kernel

theorem chunk34_checked : AllChecked state298 chunk34 :=
  ⟨(by rfl), ⟨checked299, ⟨checked300, ⟨(by rfl), ⟨checked302, ⟨(by rfl), ⟨checked304, ⟨(by rfl), ⟨checked306, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
