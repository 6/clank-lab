import CubelikeSC.Main
import CubelikeSC.R1
import CubelikeSC.Cert.Driver
import CubelikeSC.Cert.Checked
import CubelikeSC.Cert.Covered

/-!
# Lemma F and the endpoint, proved

`Cert.certs_checked` collects the kernel checks of the 3,984 certificate
entries, `Cert.all_covered` maps every case `(n, B, t)` to its entry, and
`Cert.lemmaF_of_certs` (weak duality) turns both into `LemmaF`.
-/

namespace CubelikeSC

/-- Lemma F of the paper. -/
theorem lemmaF : LemmaF :=
  Cert.lemmaF_of_certs Cert.certs Cert.certs_checked Cert.all_covered

/-- The theorem of the paper: every connection set `S ⊆ Z_2^7 \ {0}` has `|K(S)| ≤ 4`. -/
theorem endpoint : Endpoint := main lemmaF

/-- The theorem of the paper, stated for strongly cospectral vertices: in
`Cay(Z_2^7, S)`, every set `P` of pairwise strongly cospectral vertices has at
most 4 elements. For `p ∈ P`, R1 puts `P - p` inside `K(S)`. -/
theorem endpoint_sc : ∀ S : Finset V, (0 : V) ∉ S → ∀ P : Finset V,
    (∀ u ∈ P, ∀ v ∈ P, StronglyCospectral S u v) → P.card ≤ 4 := by
  intro S hS P hP
  rcases P.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hsub : P.image (fun v => v - p) ⊆ K S := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hg
    exact sub_mem_K_of_sc (hP p hp v hv)
  calc P.card = (P.image (fun v => v - p)).card :=
        (Finset.card_image_of_injective _ (sub_left_injective)).symm
    _ ≤ (K S).card := Finset.card_le_card hsub
    _ ≤ 4 := endpoint S hS

example : EndpointSC := endpoint_sc

end CubelikeSC
