import CubelikeSC.Cert.Data.N101

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c101_00 : e101_00.check = true := by decide +kernel
theorem c101_01 : e101_01.check = true := by decide +kernel
theorem c101_02 : e101_02.check = true := by decide +kernel
theorem c101_03 : e101_03.check = true := by decide +kernel
theorem c101_04 : e101_04.check = true := by decide +kernel
theorem c101_05 : e101_05.check = true := by decide +kernel
theorem c101_06 : e101_06.check = true := by decide +kernel
theorem c101_07 : e101_07.check = true := by decide +kernel
theorem c101_08 : e101_08.check = true := by decide +kernel
theorem c101_09 : e101_09.check = true := by decide +kernel
theorem c101_10 : e101_10.check = true := by decide +kernel
theorem c101_11 : e101_11.check = true := by decide +kernel
theorem c101_12 : e101_12.check = true := by decide +kernel
theorem c101_13 : e101_13.check = true := by decide +kernel
theorem c101_14 : e101_14.check = true := by decide +kernel
theorem c101_15 : e101_15.check = true := by decide +kernel
theorem c101_16 : e101_16.check = true := by decide +kernel
theorem c101_17 : e101_17.check = true := by decide +kernel
theorem c101_18 : e101_18.check = true := by decide +kernel
theorem c101_19 : e101_19.check = true := by decide +kernel
theorem c101_20 : e101_20.check = true := by decide +kernel
theorem c101_21 : e101_21.check = true := by decide +kernel
theorem c101_22 : e101_22.check = true := by decide +kernel
theorem c101_23 : e101_23.check = true := by decide +kernel
theorem c101_24 : e101_24.check = true := by decide +kernel
theorem c101_25 : e101_25.check = true := by decide +kernel
theorem c101_26 : e101_26.check = true := by decide +kernel
theorem c101_27 : e101_27.check = true := by decide +kernel
theorem c101_28 : e101_28.check = true := by decide +kernel
theorem c101_29 : e101_29.check = true := by decide +kernel
theorem c101_30 : e101_30.check = true := by decide +kernel
theorem c101_31 : e101_31.check = true := by decide +kernel

theorem check101 : entries101.all Entry.check = true := by
  simp only [entries101, List.all_cons, List.all_nil, Bool.and_true, c101_00, c101_01, c101_02, c101_03, c101_04, c101_05, c101_06, c101_07, c101_08, c101_09, c101_10, c101_11, c101_12, c101_13, c101_14, c101_15, c101_16, c101_17, c101_18, c101_19, c101_20, c101_21, c101_22, c101_23, c101_24, c101_25, c101_26, c101_27, c101_28, c101_29, c101_30, c101_31]

end CubelikeSC.Cert
