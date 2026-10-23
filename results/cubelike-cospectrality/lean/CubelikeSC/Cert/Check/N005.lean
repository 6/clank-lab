import CubelikeSC.Cert.Data.N005

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c005_00 : e005_00.check = true := by decide +kernel
theorem c005_01 : e005_01.check = true := by decide +kernel
theorem c005_02 : e005_02.check = true := by decide +kernel
theorem c005_03 : e005_03.check = true := by decide +kernel
theorem c005_04 : e005_04.check = true := by decide +kernel
theorem c005_05 : e005_05.check = true := by decide +kernel
theorem c005_06 : e005_06.check = true := by decide +kernel
theorem c005_07 : e005_07.check = true := by decide +kernel
theorem c005_08 : e005_08.check = true := by decide +kernel
theorem c005_09 : e005_09.check = true := by decide +kernel
theorem c005_10 : e005_10.check = true := by decide +kernel
theorem c005_11 : e005_11.check = true := by decide +kernel
theorem c005_12 : e005_12.check = true := by decide +kernel
theorem c005_13 : e005_13.check = true := by decide +kernel
theorem c005_14 : e005_14.check = true := by decide +kernel
theorem c005_15 : e005_15.check = true := by decide +kernel
theorem c005_16 : e005_16.check = true := by decide +kernel
theorem c005_17 : e005_17.check = true := by decide +kernel
theorem c005_18 : e005_18.check = true := by decide +kernel
theorem c005_19 : e005_19.check = true := by decide +kernel
theorem c005_20 : e005_20.check = true := by decide +kernel
theorem c005_21 : e005_21.check = true := by decide +kernel
theorem c005_22 : e005_22.check = true := by decide +kernel
theorem c005_23 : e005_23.check = true := by decide +kernel
theorem c005_24 : e005_24.check = true := by decide +kernel
theorem c005_25 : e005_25.check = true := by decide +kernel
theorem c005_26 : e005_26.check = true := by decide +kernel

theorem check005 : entries005.all Entry.check = true := by
  simp only [entries005, List.all_cons, List.all_nil, Bool.and_true, c005_00, c005_01, c005_02, c005_03, c005_04, c005_05, c005_06, c005_07, c005_08, c005_09, c005_10, c005_11, c005_12, c005_13, c005_14, c005_15, c005_16, c005_17, c005_18, c005_19, c005_20, c005_21, c005_22, c005_23, c005_24, c005_25, c005_26]

end CubelikeSC.Cert
