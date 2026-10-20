import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked89 : stepCheck state89 step89 = true := by decide +kernel
theorem checked91 : stepCheck state91 step91 = true := by decide +kernel
theorem checked93 : stepCheck state93 step93 = true := by decide +kernel
theorem checked95 : stepCheck state95 step95 = true := by decide +kernel
theorem checked97 : stepCheck state97 step97 = true := by decide +kernel

theorem chunk11_checked : AllChecked state88 chunk11 :=
  ⟨(by rfl), ⟨checked89, ⟨(by rfl), ⟨checked91, ⟨(by rfl), ⟨checked93, ⟨(by rfl), ⟨checked95, ⟨(by rfl), ⟨checked97, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
