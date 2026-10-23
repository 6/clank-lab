import CubelikeSC.Cert.Data.N100

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c100_00 : e100_00.check = true := by decide +kernel
theorem c100_01 : e100_01.check = true := by decide +kernel
theorem c100_02 : e100_02.check = true := by decide +kernel
theorem c100_03 : e100_03.check = true := by decide +kernel
theorem c100_04 : e100_04.check = true := by decide +kernel
theorem c100_05 : e100_05.check = true := by decide +kernel
theorem c100_06 : e100_06.check = true := by decide +kernel
theorem c100_07 : e100_07.check = true := by decide +kernel
theorem c100_08 : e100_08.check = true := by decide +kernel
theorem c100_09 : e100_09.check = true := by decide +kernel
theorem c100_10 : e100_10.check = true := by decide +kernel
theorem c100_11 : e100_11.check = true := by decide +kernel
theorem c100_12 : e100_12.check = true := by decide +kernel
theorem c100_13 : e100_13.check = true := by decide +kernel
theorem c100_14 : e100_14.check = true := by decide +kernel
theorem c100_15 : e100_15.check = true := by decide +kernel
theorem c100_16 : e100_16.check = true := by decide +kernel
theorem c100_17 : e100_17.check = true := by decide +kernel
theorem c100_18 : e100_18.check = true := by decide +kernel
theorem c100_19 : e100_19.check = true := by decide +kernel
theorem c100_20 : e100_20.check = true := by decide +kernel
theorem c100_21 : e100_21.check = true := by decide +kernel
theorem c100_22 : e100_22.check = true := by decide +kernel
theorem c100_23 : e100_23.check = true := by decide +kernel
theorem c100_24 : e100_24.check = true := by decide +kernel
theorem c100_25 : e100_25.check = true := by decide +kernel
theorem c100_26 : e100_26.check = true := by decide +kernel
theorem c100_27 : e100_27.check = true := by decide +kernel
theorem c100_28 : e100_28.check = true := by decide +kernel
theorem c100_29 : e100_29.check = true := by decide +kernel
theorem c100_30 : e100_30.check = true := by decide +kernel
theorem c100_31 : e100_31.check = true := by decide +kernel

theorem check100 : entries100.all Entry.check = true := by
  simp only [entries100, List.all_cons, List.all_nil, Bool.and_true, c100_00, c100_01, c100_02, c100_03, c100_04, c100_05, c100_06, c100_07, c100_08, c100_09, c100_10, c100_11, c100_12, c100_13, c100_14, c100_15, c100_16, c100_17, c100_18, c100_19, c100_20, c100_21, c100_22, c100_23, c100_24, c100_25, c100_26, c100_27, c100_28, c100_29, c100_30, c100_31]

end CubelikeSC.Cert
