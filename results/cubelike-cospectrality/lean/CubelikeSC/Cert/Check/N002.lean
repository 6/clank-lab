import CubelikeSC.Cert.Data.N002

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c002_00 : e002_00.check = true := by decide +kernel
theorem c002_01 : e002_01.check = true := by decide +kernel
theorem c002_02 : e002_02.check = true := by decide +kernel
theorem c002_03 : e002_03.check = true := by decide +kernel
theorem c002_04 : e002_04.check = true := by decide +kernel
theorem c002_05 : e002_05.check = true := by decide +kernel
theorem c002_06 : e002_06.check = true := by decide +kernel
theorem c002_07 : e002_07.check = true := by decide +kernel
theorem c002_08 : e002_08.check = true := by decide +kernel

theorem check002 : entries002.all Entry.check = true := by
  simp only [entries002, List.all_cons, List.all_nil, Bool.and_true, c002_00, c002_01, c002_02, c002_03, c002_04, c002_05, c002_06, c002_07, c002_08]

end CubelikeSC.Cert
