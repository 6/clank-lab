import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked21 : stepCheck state21 step21 = true := by decide +kernel
theorem checked22 : stepCheck state22 step22 = true := by decide +kernel
theorem checked23 : stepCheck state23 step23 = true := by decide +kernel
theorem checked25 : stepCheck state25 step25 = true := by decide +kernel
theorem checked27 : stepCheck state27 step27 = true := by decide +kernel

theorem chunk3_checked : AllChecked state21 chunk3 :=
  ⟨checked21, ⟨checked22, ⟨checked23, ⟨(by rfl), ⟨checked25, ⟨(by rfl), ⟨checked27, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
