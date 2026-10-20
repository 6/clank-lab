import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked119 : stepCheck state119 step119 = true := by decide +kernel
theorem checked121 : stepCheck state121 step121 = true := by decide +kernel
theorem checked122 : stepCheck state122 step122 = true := by decide +kernel
theorem checked123 : stepCheck state123 step123 = true := by decide +kernel
theorem checked125 : stepCheck state125 step125 = true := by decide +kernel

theorem chunk14_checked : AllChecked state118 chunk14 :=
  ⟨(by rfl), ⟨checked119, ⟨(by rfl), ⟨checked121, ⟨checked122, ⟨checked123, ⟨(by rfl), ⟨checked125, True.intro⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
