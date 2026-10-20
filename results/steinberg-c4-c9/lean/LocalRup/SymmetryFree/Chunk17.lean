import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked143 : stepCheck state143 step143 = true := by decide +kernel
theorem checked144 : stepCheck state144 step144 = true := by decide +kernel
theorem checked146 : stepCheck state146 step146 = true := by decide +kernel
theorem checked148 : stepCheck state148 step148 = true := by decide +kernel
theorem checked150 : stepCheck state150 step150 = true := by decide +kernel

theorem chunk17_checked : AllChecked state142 chunk17 :=
  ⟨(by rfl), ⟨checked143, ⟨checked144, ⟨(by rfl), ⟨checked146, ⟨(by rfl), ⟨checked148, ⟨(by rfl), ⟨checked150, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
