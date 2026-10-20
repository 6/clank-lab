import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked244 : stepCheck state244 step244 = true := by decide +kernel
theorem checked245 : stepCheck state245 step245 = true := by decide +kernel
theorem checked246 : stepCheck state246 step246 = true := by decide +kernel
theorem checked248 : stepCheck state248 step248 = true := by decide +kernel
theorem checked250 : stepCheck state250 step250 = true := by decide +kernel

theorem chunk28_checked : AllChecked state243 chunk28 :=
  ⟨(by rfl), ⟨checked244, ⟨checked245, ⟨checked246, ⟨(by rfl), ⟨checked248, ⟨(by rfl), ⟨checked250, True.intro⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
