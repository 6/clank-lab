import SourceRegularity

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- First perturbation, CENTRAL cell only, with source regularity and
    the full envelope supplied by exact finite source/chart certificates. -/
theorem first_source_ordered_iff {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (S : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0)
    (f : Fin (d + 1) → Fin n) (hf : Function.Injective f) :
    ActiveRay (chartedGenericFactor A C) none (fun j => f j.succ) ↔
      ActiveRay (A.map (Int.castRingHom ℚ)) none (fun j => f j.succ) := by
  unfold chartedGenericFactor
  rw [chart_active_iff _ _ (by exact_mod_cast h0)]
  let D : Matrix (Fin n) (Fin (d + 1)) ℤ := integerVandermonde
  let B := starEnvelope A D C
  have hb := starEnvelope_bounds A D C
  have hp := integer_minor_nonzero A f hf
  have hr := source_regularOrderedLabel A S i₀ ha f (hf.comp (Fin.succ_injective _))
  have hu := explicit_uniform_specialization (by omega : 0 < d + 1) A B
    hb.1 hb.2.1 hb.2.2.1 f hf
  have he : IntegralActiveRay A none (fun j => f j.succ) ↔
      ActiveRay (specializedMatrix A D (commonParameter (d + 1) B)) none (fun j => f j.succ) := by
    constructor
    · rintro ⟨v, hv, hfeas, hactive⟩
      obtain ⟨w, hw, hfw, haw⟩ := old_ray_has_specialized_label A D f (starUnit none) B
        hb.1 hb.2.1 hb.2.2.1 hp hr hu v hv hfeas hactive
      refine ⟨w, hw, ?_, haw⟩
      intro i
      simpa [starUnit, starSign] using hfw i
    · rintro ⟨v, hv, hfeas, hactive⟩
      have hf' : ∀ i, 0 ≤ ((starUnit none i : ℤ) : ℚ) *
          (specializedMatrix A D (commonParameter (d + 1) B) i ⬝ᵥ v) := by
        intro i
        simpa [starUnit, starSign] using hfeas i
      obtain ⟨w, hw, hfw, haw, _⟩ := specialized_ray_has_old_label A D f (starUnit none) B
        hb.1 hb.2.1 hb.2.2.1 hp hr hu v hv hf' hactive
      exact ⟨w, hw, hfw, haw⟩
  exact he.symm.trans (integral_ray_field_iff A none _)

theorem first_source_label_iff {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (S : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (hn : d < n)
    (label : Fin d → Fin n) (hl : Function.Injective label) :
    ActiveRay (chartedGenericFactor A C) none label ↔
      ActiveRay (A.map (Int.castRingHom ℚ)) none label := by
  classical
  have hc : (univ.image label).card < (univ : Finset (Fin n)).card := by
    simpa [Finset.card_image_of_injective _ hl] using hn
  obtain ⟨i, _, hi⟩ := exists_mem_not_mem_of_card_lt_card hc
  have hinj : Function.Injective (Fin.cons i label) :=
    Fin.cons_injective_iff.mpr ⟨by simpa using hi, hl⟩
  exact first_source_ordered_iff A C h0 S i₀ ha (Fin.cons i label) hinj

/-- The exact same finite points and neighbor indices certify the old
    real homogeneous source; the field change discharges every premise. -/
def realSourceCertificate {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (S : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V) :
    SourceVertexCertificate (sourceSpatial (A.map (Rat.castHom ℝ)))
      (sourceBound (A.map (Rat.castHom ℝ))) V := by
  simpa only [sourceSpatial, sourceBound, Matrix.map_apply, Rat.coe_castHom, Rat.cast_neg] using S.toReal

/-- First-factor label preservation covers ALL real central rays in
    both directions, rather than only rational samples or old vertices. -/
theorem first_source_real_label_iff {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (S : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (hn : d < n)
    (label : Fin d → Fin n) (hl : Function.Injective label) :
    ActiveRay ((chartedGenericFactor A C).map (Rat.castHom ℝ)) none label ↔
      ActiveRay ((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none label := by
  have hp := chartedGenericFactor_real_properties A C h0
  have hnew := uniform_real_active_iff (chartedGenericFactor A C) hn hp.1 hp.2 none label hl
  have hold : ActiveRay ((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none label ↔
      ActiveRay (A.map (Int.castRingHom ℚ)) none label := by
    apply real_active_iff
    intro v hv hf hx
    have hr := source_homogeneous_regularity _ (realSourceCertificate _ S) i₀
      (fun i => by change (0 : ℝ) < ((A i 0 : ℚ) : ℝ); exact_mod_cast ha i) v hv hf label hl hx
    exact ⟨hr.1, hr.2.1⟩
  exact hnew.trans ((first_source_label_iff A C h0 S i₀ ha hn label hl).trans hold.symm)

#print axioms first_source_label_iff
#print axioms realSourceCertificate
#print axioms first_source_real_label_iff
end
end ADKZPricing
