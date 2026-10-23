import CubelikeSC.Cert.Key
import CubelikeSC.Cert.Certs

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem cov035_0 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨0, by decide⟩ = true := by decide +kernel
theorem cov035_1 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨1, by decide⟩ = true := by decide +kernel
theorem cov035_2 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨2, by decide⟩ = true := by decide +kernel
theorem cov035_3 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨3, by decide⟩ = true := by decide +kernel
theorem cov035_4 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨4, by decide⟩ = true := by decide +kernel
theorem cov035_5 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨5, by decide⟩ = true := by decide +kernel
theorem cov035_6 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨6, by decide⟩ = true := by decide +kernel
theorem cov035_7 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 35 →
    covered certs 35 B ⟨7, by decide⟩ = true := by decide +kernel

theorem cov035 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, B.card ≤ 35 →
    covered certs 35 B t = true := by
  intro B hB t hc
  match t with
  | ⟨0, _⟩ => exact cov035_0 B hB hc
  | ⟨1, _⟩ => exact cov035_1 B hB hc
  | ⟨2, _⟩ => exact cov035_2 B hB hc
  | ⟨3, _⟩ => exact cov035_3 B hB hc
  | ⟨4, _⟩ => exact cov035_4 B hB hc
  | ⟨5, _⟩ => exact cov035_5 B hB hc
  | ⟨6, _⟩ => exact cov035_6 B hB hc
  | ⟨7, _⟩ => exact cov035_7 B hB hc
  | ⟨k + 8, h⟩ => exact absurd h (by omega)

end CubelikeSC.Cert
