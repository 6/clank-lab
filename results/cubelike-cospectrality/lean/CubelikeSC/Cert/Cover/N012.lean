import CubelikeSC.Cert.Key
import CubelikeSC.Cert.Certs

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

theorem cov012_0 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨0, by decide⟩ = true := by decide +kernel
theorem cov012_1 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨1, by decide⟩ = true := by decide +kernel
theorem cov012_2 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨2, by decide⟩ = true := by decide +kernel
theorem cov012_3 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨3, by decide⟩ = true := by decide +kernel
theorem cov012_4 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨4, by decide⟩ = true := by decide +kernel
theorem cov012_5 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨5, by decide⟩ = true := by decide +kernel
theorem cov012_6 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨6, by decide⟩ = true := by decide +kernel
theorem cov012_7 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → B.card ≤ 12 →
    covered certs 12 B ⟨7, by decide⟩ = true := by decide +kernel

theorem cov012 : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, B.card ≤ 12 →
    covered certs 12 B t = true := by
  intro B hB t hc
  match t with
  | ⟨0, _⟩ => exact cov012_0 B hB hc
  | ⟨1, _⟩ => exact cov012_1 B hB hc
  | ⟨2, _⟩ => exact cov012_2 B hB hc
  | ⟨3, _⟩ => exact cov012_3 B hB hc
  | ⟨4, _⟩ => exact cov012_4 B hB hc
  | ⟨5, _⟩ => exact cov012_5 B hB hc
  | ⟨6, _⟩ => exact cov012_6 B hB hc
  | ⟨7, _⟩ => exact cov012_7 B hB hc
  | ⟨k + 8, h⟩ => exact absurd h (by omega)

end CubelikeSC.Cert
