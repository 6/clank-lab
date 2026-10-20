import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked251 : stepCheck state251 step251 = true := by decide +kernel
theorem checked252 : stepCheck state252 step252 = true := by decide +kernel
theorem checked254 : stepCheck state254 step254 = true := by decide +kernel
theorem checked256 : stepCheck state256 step256 = true := by decide +kernel
theorem checked258 : stepCheck state258 step258 = true := by decide +kernel

theorem chunk29_checked : AllChecked state251 chunk29 :=
  ⟨checked251, ⟨checked252, ⟨(by rfl), ⟨checked254, ⟨(by rfl), ⟨checked256, ⟨(by rfl), ⟨checked258, True.intro⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
