import CubelikeSC.Cert.Key
import CubelikeSC.Cert.Certs

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem cov049_0 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨0, by decide⟩ = true := by decide +kernel
theorem cov049_1 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨1, by decide⟩ = true := by decide +kernel
theorem cov049_2 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨2, by decide⟩ = true := by decide +kernel
theorem cov049_3 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨3, by decide⟩ = true := by decide +kernel
theorem cov049_4 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨4, by decide⟩ = true := by decide +kernel
theorem cov049_5 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨5, by decide⟩ = true := by decide +kernel
theorem cov049_6 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨6, by decide⟩ = true := by decide +kernel
theorem cov049_7 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 49 →
    covered certs 49 B ⟨7, by decide⟩ = true := by decide +kernel

theorem cov049 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, B.card ≤ 49 →
    covered certs 49 B t = true := by
  intro B hB t hc
  match t with
  | ⟨0, _⟩ => exact cov049_0 B hB hc
  | ⟨1, _⟩ => exact cov049_1 B hB hc
  | ⟨2, _⟩ => exact cov049_2 B hB hc
  | ⟨3, _⟩ => exact cov049_3 B hB hc
  | ⟨4, _⟩ => exact cov049_4 B hB hc
  | ⟨5, _⟩ => exact cov049_5 B hB hc
  | ⟨6, _⟩ => exact cov049_6 B hB hc
  | ⟨7, _⟩ => exact cov049_7 B hB hc
  | ⟨k + 8, h⟩ => exact absurd h (by omega)

end CubelikeSC.Cert
