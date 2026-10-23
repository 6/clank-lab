import CubelikeSC.Cert.Data.N006

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c006_00 : e006_00.check = true := by decide +kernel
theorem c006_01 : e006_01.check = true := by decide +kernel
theorem c006_02 : e006_02.check = true := by decide +kernel
theorem c006_03 : e006_03.check = true := by decide +kernel
theorem c006_04 : e006_04.check = true := by decide +kernel
theorem c006_05 : e006_05.check = true := by decide +kernel
theorem c006_06 : e006_06.check = true := by decide +kernel
theorem c006_07 : e006_07.check = true := by decide +kernel
theorem c006_08 : e006_08.check = true := by decide +kernel
theorem c006_09 : e006_09.check = true := by decide +kernel
theorem c006_10 : e006_10.check = true := by decide +kernel
theorem c006_11 : e006_11.check = true := by decide +kernel
theorem c006_12 : e006_12.check = true := by decide +kernel
theorem c006_13 : e006_13.check = true := by decide +kernel
theorem c006_14 : e006_14.check = true := by decide +kernel
theorem c006_15 : e006_15.check = true := by decide +kernel
theorem c006_16 : e006_16.check = true := by decide +kernel
theorem c006_17 : e006_17.check = true := by decide +kernel
theorem c006_18 : e006_18.check = true := by decide +kernel
theorem c006_19 : e006_19.check = true := by decide +kernel
theorem c006_20 : e006_20.check = true := by decide +kernel
theorem c006_21 : e006_21.check = true := by decide +kernel
theorem c006_22 : e006_22.check = true := by decide +kernel
theorem c006_23 : e006_23.check = true := by decide +kernel
theorem c006_24 : e006_24.check = true := by decide +kernel
theorem c006_25 : e006_25.check = true := by decide +kernel
theorem c006_26 : e006_26.check = true := by decide +kernel
theorem c006_27 : e006_27.check = true := by decide +kernel
theorem c006_28 : e006_28.check = true := by decide +kernel
theorem c006_29 : e006_29.check = true := by decide +kernel

theorem check006 : entries006.all Entry.check = true := by
  simp only [entries006, List.all_cons, List.all_nil, Bool.and_true, c006_00, c006_01, c006_02, c006_03, c006_04, c006_05, c006_06, c006_07, c006_08, c006_09, c006_10, c006_11, c006_12, c006_13, c006_14, c006_15, c006_16, c006_17, c006_18, c006_19, c006_20, c006_21, c006_22, c006_23, c006_24, c006_25, c006_26, c006_27, c006_28, c006_29]

end CubelikeSC.Cert
