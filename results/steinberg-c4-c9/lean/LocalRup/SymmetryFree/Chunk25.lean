import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked215 : stepCheck state215 step215 = true := by decide +kernel
theorem checked217 : stepCheck state217 step217 = true := by decide +kernel
theorem checked219 : stepCheck state219 step219 = true := by decide +kernel
theorem checked221 : stepCheck state221 step221 = true := by decide +kernel
theorem checked223 : stepCheck state223 step223 = true := by decide +kernel

theorem chunk25_checked : AllChecked state215 chunk25 :=
  ⟨checked215, ⟨(by rfl), ⟨checked217, ⟨(by rfl), ⟨checked219, ⟨(by rfl), ⟨checked221, ⟨(by rfl), ⟨checked223, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
