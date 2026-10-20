import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked191 : stepCheck state191 step191 = true := by decide +kernel
theorem checked192 : stepCheck state192 step192 = true := by decide +kernel
theorem checked193 : stepCheck state193 step193 = true := by decide +kernel
theorem checked194 : stepCheck state194 step194 = true := by decide +kernel
theorem checked195 : stepCheck state195 step195 = true := by decide +kernel

theorem chunk22_checked : AllChecked state190 chunk22 :=
  ⟨(by rfl), ⟨checked191, ⟨checked192, ⟨checked193, ⟨checked194, ⟨checked195, True.intro⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
