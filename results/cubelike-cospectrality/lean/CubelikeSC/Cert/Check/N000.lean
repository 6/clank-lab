import CubelikeSC.Cert.Data.N000

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem c000_00 : e000_00.check = true := by decide +kernel
theorem c000_01 : e000_01.check = true := by decide +kernel

theorem check000 : entries000.all Entry.check = true := by
  simp only [entries000, List.all_cons, List.all_nil, Bool.and_true, c000_00, c000_01]

end CubelikeSC.Cert
