import RayPreservation

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- All original product-star signs share this integer-to-specialized
    active-label equivalence. Regularity, the common envelope and both
    nonzero-minor obligations are supplied from the first construction. -/
theorem second_active_label_equivalence {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (f : Fin (d + d + 1) → Fin (n + n))
    (hf : Function.Injective f) :
    let P := secondIntegralMatrix A C
    let B := starEnvelope P integerVandermonde (secondIntegralChart A C h0)
    let N := specializedMatrix P integerVandermonde (commonParameter (d + d + 1) B)
    (∃ v : Fin (d + d + 1) → ℤ, (∃ j, v j ≠ 0) ∧
      (∀ i, 0 ≤ (starUnit c i : ℤ) * ∑ j, P i j * v j) ∧
      (∀ j : Fin (d + d), ∑ k, P (f j.succ) k * v k = 0)) ↔
    (∃ v : Fin (d + d + 1) → ℚ, v ≠ 0 ∧
      (∀ i, 0 ≤ (starUnit c i : ℤ) * (N i ⬝ᵥ v)) ∧
      (∀ j : Fin (d + d), N (f j.succ) ⬝ᵥ v = 0)) := by
  let P := secondIntegralMatrix A C
  let D : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℤ := integerVandermonde
  let B := starEnvelope P D (secondIntegralChart A C h0)
  have hb := starEnvelope_bounds P D (secondIntegralChart A C h0)
  have hp := integer_minor_nonzero P f hf
  have hr := secondIntegral_regularity A C h0 hn c f (hf.comp (Fin.succ_injective _))
  have hu := explicit_uniform_specialization (by omega : 0 < d + d + 1) P B
    hb.1 hb.2.1 hb.2.2.1 f hf
  constructor
  · rintro ⟨v, hv, hfeas, hactive⟩
    exact old_ray_has_specialized_label P D f (starUnit c) B hb.1 hb.2.1 hb.2.2.1
      hp hr hu v hv hfeas hactive
  · rintro ⟨v, hv, hfeas, hactive⟩
    obtain ⟨w, hw, hfeas', hactive', _⟩ := specialized_ray_has_old_label P D f (starUnit c)
      B hb.1 hb.2.1 hb.2.2.1 hp hr hu v hv hfeas hactive
    exact ⟨w, hw, hfeas', hactive'⟩

#print axioms second_active_label_equivalence
end
end ADKZPricing
