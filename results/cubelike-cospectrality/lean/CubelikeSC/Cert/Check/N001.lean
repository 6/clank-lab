import CubelikeSC.Cert.Data.N001

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c001_00 : e001_00.check = true := by decide +kernel
theorem c001_01 : e001_01.check = true := by decide +kernel
theorem c001_02 : e001_02.check = true := by decide +kernel
theorem c001_03 : e001_03.check = true := by decide +kernel
theorem c001_04 : e001_04.check = true := by decide +kernel

theorem check001 : entries001.all Entry.check = true := by
  simp only [entries001, List.all_cons, List.all_nil, Bool.and_true, c001_00, c001_01, c001_02, c001_03, c001_04]

end CubelikeSC.Cert
