import Mathlib
import P16c.Polytope

/-! # Polytopes and regularity transfer along rank-preserving order isomorphisms -/

namespace P16c

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q]

lemma flag_map_symm (e : P ≃o Q) (Φ : Flag Q) : Flag.map e (Flag.map e.symm Φ) = Φ :=
  (Flag.map e).apply_symm_apply Φ

lemma coe_flag_eq (e : P ≃o Q) (Φ : Flag Q) :
    (Φ : Set Q) = e '' (Flag.map e.symm Φ : Set P) := by
  conv_lhs => rw [← flag_map_symm e Φ]
  rfl

lemma FlagAdjacent.map (e : P ≃o Q) {A B : Flag P} (h : FlagAdjacent A B) :
    FlagAdjacent (Flag.map e A) (Flag.map e B) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨e F, ?_⟩
  rw [Flag.coe_map, Flag.coe_map, ← Set.image_sdiff e.injective, hF, Set.image_singleton]

theorem IsPolytope.of_orderIso {n : ℕ} {rP : P → ℤ} {rQ : Q → ℤ} (hP : IsPolytope P n rP)
    (e : P ≃o Q) (he : ∀ F, rQ (e F) = rP F) : IsPolytope Q n rQ := by
  have he' : ∀ G, rQ G = rP (e.symm G) := fun G => by rw [← he, e.apply_symm_apply]
  refine ⟨fun a b hab => ?_, fun F => ?_, ?_, ?_, fun Φ => ?_, fun Φ Ψ => ?_, fun F G hFG hr => ?_⟩
  · rw [he', he']; exact hP.rank_strictMono (e.symm.strictMono hab)
  · rw [he']; exact hP.rank_mem _
  · obtain ⟨F, hF⟩ := hP.exists_least
    exact ⟨e F, fun G => by rw [← e.apply_symm_apply G]; exact e.monotone (hF _)⟩
  · obtain ⟨F, hF⟩ := hP.exists_greatest
    exact ⟨e F, fun G => by rw [← e.apply_symm_apply G]; exact e.monotone (hF _)⟩
  · rw [coe_flag_eq e Φ, Set.ncard_image_of_injective _ e.injective]
    exact hP.flag_ncard _
  · have h := hP.strongly_flag_connected (Flag.map e.symm Φ) (Flag.map e.symm Ψ)
    rw [← flag_map_symm e Φ, ← flag_map_symm e Ψ]
    refine h.lift (Flag.map e) (fun A B hAB => ⟨hAB.1.map e, ?_⟩)
    rw [Flag.coe_map, Flag.coe_map, Flag.coe_map, ← Set.image_inter e.injective]
    exact Set.image_mono hAB.2
  · have hlt : e.symm F < e.symm G := e.symm.strictMono hFG
    have hd := hP.diamond _ _ hlt (by rw [← he', ← he', hr])
    rw [← hd, ← Set.ncard_image_of_injective _ e.injective]
    congr 1
    ext H
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e.symm H, ⟨e.symm.strictMono h1, e.symm.strictMono h2⟩, e.apply_symm_apply H⟩
    · rintro ⟨H', ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using e.strictMono h1, by simpa using e.strictMono h2⟩

theorem IsRegular.of_orderIso (hP : IsRegular P) (e : P ≃o Q) : IsRegular Q := by
  intro Φ Ψ
  obtain ⟨σ, hσ⟩ := hP (Flag.map e.symm Φ) (Flag.map e.symm Ψ)
  refine ⟨e.symm.trans (σ.trans e), ?_⟩
  rw [← flag_map_symm e Ψ, ← hσ]
  apply Flag.ext
  simp only [Flag.coe_map, Set.image_image]
  rfl

end P16c
