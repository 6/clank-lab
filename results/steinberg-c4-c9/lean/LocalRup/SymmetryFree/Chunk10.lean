import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked80 : stepCheck state80 step80 = true := by decide +kernel
theorem checked82 : stepCheck state82 step82 = true := by decide +kernel
theorem checked84 : stepCheck state84 step84 = true := by decide +kernel
theorem checked86 : stepCheck state86 step86 = true := by decide +kernel
theorem checked87 : stepCheck state87 step87 = true := by decide +kernel

theorem chunk10_checked : AllChecked state79 chunk10 :=
  ⟨(by rfl), ⟨checked80, ⟨(by rfl), ⟨checked82, ⟨(by rfl), ⟨checked84, ⟨(by rfl), ⟨checked86, ⟨checked87, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
