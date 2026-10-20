import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked152 : stepCheck state152 step152 = true := by decide +kernel
theorem checked154 : stepCheck state154 step154 = true := by decide +kernel
theorem checked156 : stepCheck state156 step156 = true := by decide +kernel
theorem checked158 : stepCheck state158 step158 = true := by decide +kernel
theorem checked160 : stepCheck state160 step160 = true := by decide +kernel

theorem chunk18_checked : AllChecked state151 chunk18 :=
  ⟨(by rfl), ⟨checked152, ⟨(by rfl), ⟨checked154, ⟨(by rfl), ⟨checked156, ⟨(by rfl), ⟨checked158, ⟨(by rfl), ⟨checked160, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
