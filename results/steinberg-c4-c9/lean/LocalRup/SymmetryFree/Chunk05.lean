import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked38 : stepCheck state38 step38 = true := by decide +kernel
theorem checked40 : stepCheck state40 step40 = true := by decide +kernel
theorem checked41 : stepCheck state41 step41 = true := by decide +kernel
theorem checked43 : stepCheck state43 step43 = true := by decide +kernel
theorem checked44 : stepCheck state44 step44 = true := by decide +kernel

theorem chunk5_checked : AllChecked state38 chunk5 :=
  ⟨checked38, ⟨(by rfl), ⟨checked40, ⟨checked41, ⟨(by rfl), ⟨checked43, ⟨checked44, True.intro⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
