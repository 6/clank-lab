import LocalRup.SymmetryFree.Data

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked318 : stepCheck state318 step318 = true := by decide +kernel
theorem checked320 : stepCheck state320 step320 = true := by decide +kernel
theorem checked322 : stepCheck state322 step322 = true := by decide +kernel
theorem checked324 : stepCheck state324 step324 = true := by decide +kernel
theorem checked326 : stepCheck state326 step326 = true := by decide +kernel

theorem chunk36_checked : AllChecked state317 chunk36 :=
  ⟨(by rfl), ⟨checked318, ⟨(by rfl), ⟨checked320, ⟨(by rfl), ⟨checked322, ⟨(by rfl), ⟨checked324, ⟨(by rfl), ⟨checked326, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end LocalRup.SymmetryFree
