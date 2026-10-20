import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked53 : stepCheck state53 step53 = true := by decide +kernel
theorem checked54 : stepCheck state54 step54 = true := by decide +kernel
theorem checked56 : stepCheck state56 step56 = true := by decide +kernel
theorem checked57 : stepCheck state57 step57 = true := by decide +kernel
theorem checked58 : stepCheck state58 step58 = true := by decide +kernel

theorem chunk7_checked : AllChecked state52 chunk7 :=
  ⟨(by rfl), ⟨checked53, ⟨checked54, ⟨(by rfl), ⟨checked56, ⟨checked57, ⟨checked58, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
