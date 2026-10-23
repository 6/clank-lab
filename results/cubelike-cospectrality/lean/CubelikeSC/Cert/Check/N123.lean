import CubelikeSC.Cert.Data.N123

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c123_00 : e123_00.check = true := by decide +kernel
theorem c123_01 : e123_01.check = true := by decide +kernel
theorem c123_02 : e123_02.check = true := by decide +kernel
theorem c123_03 : e123_03.check = true := by decide +kernel
theorem c123_04 : e123_04.check = true := by decide +kernel
theorem c123_05 : e123_05.check = true := by decide +kernel
theorem c123_06 : e123_06.check = true := by decide +kernel
theorem c123_07 : e123_07.check = true := by decide +kernel
theorem c123_08 : e123_08.check = true := by decide +kernel
theorem c123_09 : e123_09.check = true := by decide +kernel
theorem c123_10 : e123_10.check = true := by decide +kernel
theorem c123_11 : e123_11.check = true := by decide +kernel
theorem c123_12 : e123_12.check = true := by decide +kernel
theorem c123_13 : e123_13.check = true := by decide +kernel
theorem c123_14 : e123_14.check = true := by decide +kernel
theorem c123_15 : e123_15.check = true := by decide +kernel
theorem c123_16 : e123_16.check = true := by decide +kernel
theorem c123_17 : e123_17.check = true := by decide +kernel
theorem c123_18 : e123_18.check = true := by decide +kernel
theorem c123_19 : e123_19.check = true := by decide +kernel
theorem c123_20 : e123_20.check = true := by decide +kernel
theorem c123_21 : e123_21.check = true := by decide +kernel
theorem c123_22 : e123_22.check = true := by decide +kernel
theorem c123_23 : e123_23.check = true := by decide +kernel
theorem c123_24 : e123_24.check = true := by decide +kernel
theorem c123_25 : e123_25.check = true := by decide +kernel
theorem c123_26 : e123_26.check = true := by decide +kernel
theorem c123_27 : e123_27.check = true := by decide +kernel
theorem c123_28 : e123_28.check = true := by decide +kernel
theorem c123_29 : e123_29.check = true := by decide +kernel
theorem c123_30 : e123_30.check = true := by decide +kernel
theorem c123_31 : e123_31.check = true := by decide +kernel

theorem check123 : entries123.all Entry.check = true := by
  simp only [entries123, List.all_cons, List.all_nil, Bool.and_true, c123_00, c123_01, c123_02, c123_03, c123_04, c123_05, c123_06, c123_07, c123_08, c123_09, c123_10, c123_11, c123_12, c123_13, c123_14, c123_15, c123_16, c123_17, c123_18, c123_19, c123_20, c123_21, c123_22, c123_23, c123_24, c123_25, c123_26, c123_27, c123_28, c123_29, c123_30, c123_31]

end CubelikeSC.Cert
