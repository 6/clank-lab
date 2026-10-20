import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked338 : stepCheck state338 step338 = true := by decide +kernel

theorem chunk38_checked : AllChecked state337 chunk38 :=
  ⟨(by rfl), ⟨checked338, True.intro⟩⟩

end LocalRup.SymmetryFree
