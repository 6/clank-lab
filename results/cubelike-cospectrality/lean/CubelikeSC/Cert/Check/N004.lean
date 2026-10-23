import CubelikeSC.Cert.Data.N004

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c004_00 : e004_00.check = true := by decide +kernel
theorem c004_01 : e004_01.check = true := by decide +kernel
theorem c004_02 : e004_02.check = true := by decide +kernel
theorem c004_03 : e004_03.check = true := by decide +kernel
theorem c004_04 : e004_04.check = true := by decide +kernel
theorem c004_05 : e004_05.check = true := by decide +kernel
theorem c004_06 : e004_06.check = true := by decide +kernel
theorem c004_07 : e004_07.check = true := by decide +kernel
theorem c004_08 : e004_08.check = true := by decide +kernel
theorem c004_09 : e004_09.check = true := by decide +kernel
theorem c004_10 : e004_10.check = true := by decide +kernel
theorem c004_11 : e004_11.check = true := by decide +kernel
theorem c004_12 : e004_12.check = true := by decide +kernel
theorem c004_13 : e004_13.check = true := by decide +kernel
theorem c004_14 : e004_14.check = true := by decide +kernel
theorem c004_15 : e004_15.check = true := by decide +kernel
theorem c004_16 : e004_16.check = true := by decide +kernel
theorem c004_17 : e004_17.check = true := by decide +kernel
theorem c004_18 : e004_18.check = true := by decide +kernel
theorem c004_19 : e004_19.check = true := by decide +kernel
theorem c004_20 : e004_20.check = true := by decide +kernel
theorem c004_21 : e004_21.check = true := by decide +kernel
theorem c004_22 : e004_22.check = true := by decide +kernel

theorem check004 : entries004.all Entry.check = true := by
  simp only [entries004, List.all_cons, List.all_nil, Bool.and_true, c004_00, c004_01, c004_02, c004_03, c004_04, c004_05, c004_06, c004_07, c004_08, c004_09, c004_10, c004_11, c004_12, c004_13, c004_14, c004_15, c004_16, c004_17, c004_18, c004_19, c004_20, c004_21, c004_22]

end CubelikeSC.Cert
