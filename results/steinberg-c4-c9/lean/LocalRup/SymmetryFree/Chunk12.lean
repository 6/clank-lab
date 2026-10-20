import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked99 : stepCheck state99 step99 = true := by decide +kernel
theorem checked101 : stepCheck state101 step101 = true := by decide +kernel
theorem checked103 : stepCheck state103 step103 = true := by decide +kernel
theorem checked105 : stepCheck state105 step105 = true := by decide +kernel
theorem checked107 : stepCheck state107 step107 = true := by decide +kernel

theorem chunk12_checked : AllChecked state98 chunk12 :=
  ⟨(by rfl), ⟨checked99, ⟨(by rfl), ⟨checked101, ⟨(by rfl), ⟨checked103, ⟨(by rfl), ⟨checked105, ⟨(by rfl), ⟨checked107, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
