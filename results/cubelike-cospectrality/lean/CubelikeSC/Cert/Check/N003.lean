import CubelikeSC.Cert.Data.N003

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c003_00 : e003_00.check = true := by decide +kernel
theorem c003_01 : e003_01.check = true := by decide +kernel
theorem c003_02 : e003_02.check = true := by decide +kernel
theorem c003_03 : e003_03.check = true := by decide +kernel
theorem c003_04 : e003_04.check = true := by decide +kernel
theorem c003_05 : e003_05.check = true := by decide +kernel
theorem c003_06 : e003_06.check = true := by decide +kernel
theorem c003_07 : e003_07.check = true := by decide +kernel
theorem c003_08 : e003_08.check = true := by decide +kernel
theorem c003_09 : e003_09.check = true := by decide +kernel
theorem c003_10 : e003_10.check = true := by decide +kernel
theorem c003_11 : e003_11.check = true := by decide +kernel
theorem c003_12 : e003_12.check = true := by decide +kernel
theorem c003_13 : e003_13.check = true := by decide +kernel
theorem c003_14 : e003_14.check = true := by decide +kernel
theorem c003_15 : e003_15.check = true := by decide +kernel

theorem check003 : entries003.all Entry.check = true := by
  simp only [entries003, List.all_cons, List.all_nil, Bool.and_true, c003_00, c003_01, c003_02, c003_03, c003_04, c003_05, c003_06, c003_07, c003_08, c003_09, c003_10, c003_11, c003_12, c003_13, c003_14, c003_15]

end CubelikeSC.Cert
