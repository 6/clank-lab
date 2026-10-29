import ActiveChartTransport
import KernelRayTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Real active rays are covered by the canonical rational kernel, not
    merely by embedding supplied rational witnesses into the reals. -/
theorem real_active_iff {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (c : Option (Fin n)) (label : Fin d → Fin n)
    (hr : ∀ v : Fin (d + 1) → ℝ, v ≠ 0 →
      StarFeasible (A.map (Rat.castHom ℝ)) c v →
      (∀ j, (A.map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) →
      0 < v 0 ∧ ((A.map (Rat.castHom ℝ)).submatrix label Fin.succ).det ≠ 0) :
    ActiveRay (A.map (Rat.castHom ℝ)) c label ↔ ActiveRay A c label := by
  constructor
  · rintro ⟨v, hv, hf, ha⟩
    have hreg := hr v hv hf ha
    have hd := rational_minor_of_real A label Fin.succ hreg.2
    have hk := canonical_kernel_labels A label hd v hreg.1 ha
    refine ⟨affineKernel (A.submatrix label id), ?_, (hk.1 c).mp hf, ?_⟩
    · intro hz
      have he := congrFun hz 0
      simp [affineKernel] at he
    · intro j
      exact (hk.2 (label j)).mp (ha j)
  · rintro ⟨v, hv, hf, ha⟩
    let w : Fin (d + 1) → ℝ := fun j => (v j : ℝ)
    have hrow (i : Fin n) : (A.map (Rat.castHom ℝ)) i ⬝ᵥ w = ((A i ⬝ᵥ v : ℚ) : ℝ) := by
      simp [w, dotProduct, Matrix.map_apply]
    refine ⟨w, ?_, ?_, ?_⟩
    · intro hz
      apply hv
      ext j
      have he := congrFun hz j
      change (v j : ℝ) = 0 at he
      exact_mod_cast he
    · intro i
      have hs : (((starSign c i : ℚ) : ℝ)) = starSign c i := by
        unfold starSign
        split_ifs <;> norm_num
      change 0 ≤ starSign c i * ((A.map (Rat.castHom ℝ)) i ⬝ᵥ w)
      rw [hrow, ← hs]
      exact_mod_cast hf i
    · intro j
      rw [hrow, ha j, Rat.cast_zero]

/-- For a uniform strict-chart matrix the real kernel premise follows
    from actual active equations, using a single unused row. -/
theorem uniform_real_active_iff {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (hn : d < n)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f →
      ((A.map (Rat.castHom ℝ)).submatrix f id).det ≠ 0)
    (hchart : ∀ c v, StarFeasible (A.map (Rat.castHom ℝ)) c v → v ≠ 0 → 0 < v 0)
    (c : Option (Fin n)) (label : Fin d → Fin n) (hl : Function.Injective label) :
    ActiveRay (A.map (Rat.castHom ℝ)) c label ↔ ActiveRay A c label := by
  apply real_active_iff
  intro v hv hf ha
  have hp := hchart c v hf hv
  refine ⟨hp, ?_⟩
  apply uniform_charted_spatial_basis _ hn hu label hl ((v 0)⁻¹ • v)
  · simp [hp.ne']
  · intro j
    rw [dotProduct_smul, ha j, smul_zero]

/-- Remove the arbitrary extra completion row from the preservation
    statement; existence of that unused row follows from d<n. -/
theorem second_product_label_iff {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (label : Fin (d + d) → Fin (n + n))
    (hl : Function.Injective label) :
    ActiveRay (secondPerturbedMatrix A C h0) c label ↔ ActiveRay (firstProduct A C) c label := by
  classical
  have hc : (univ.image label).card < (univ : Finset (Fin (n + n))).card := by
    simpa [Finset.card_image_of_injective _ hl] using (show d + d < n + n by omega)
  obtain ⟨i, _, hi⟩ := exists_mem_not_mem_of_card_lt_card hc
  have hinj : Function.Injective (Fin.cons i label) :=
    Fin.cons_injective_iff.mpr ⟨by simpa using hi, hl⟩
  exact second_product_active_iff A C h0 hn c (Fin.cons i label) hinj

/-- ALL real rays on an active product vertex label are preserved in
    both directions, with product regularity and both strict charts
    supplied from the finite original chart. This is not a graph premise. -/
theorem second_product_real_label_iff {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (label : Fin (d + d) → Fin (n + n))
    (hl : Function.Injective label) :
    ActiveRay ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c label ↔
      ActiveRay ((firstProduct A C).map (Rat.castHom ℝ)) c label := by
  have hp := chartedGenericFactor_real_properties _ _ (secondIntegralChart_pivot A C h0)
  have hnew := uniform_real_active_iff (secondPerturbedMatrix A C h0)
    (by omega : d + d < n + n) hp.1 hp.2 c label hl
  have hold : ActiveRay ((firstProduct A C).map (Rat.castHom ℝ)) c label ↔
      ActiveRay (firstProduct A C) c label := by
    apply real_active_iff
    intro v hv hf ha
    have he := firstProduct_real_regularity A C h0 hn c v hf hv label hl ha
    exact ⟨he.1, he.2.1⟩
  exact hnew.trans ((second_product_label_iff A C h0 hn c label hl).trans hold.symm)

/-- A preserved vertex label is its COMPLETE zero set: no extra zero
    can appear under the global uniform perturbation. -/
theorem uniform_complete_active_labels {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (v : Fin (d + 1) → K) (hv : v ≠ 0)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (ha : ∀ j, A (label j) ⬝ᵥ v = 0) :
    ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Set.range label := by
  classical
  intro i
  constructor
  · intro hi
    by_contra hout
    let f : Fin (d + 1) → Fin n := Fin.cons i label
    have hf : Function.Injective f := Fin.cons_injective_iff.mpr ⟨hout, hl⟩
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hu f hf)))
    apply hv
    apply hinj
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [Matrix.mulVec, Matrix.submatrix, f] using hi
    · simpa [Matrix.mulVec, Matrix.submatrix, f] using ha k
  · rintro ⟨j, rfl⟩
    exact ha j

/-- Fold the determinant interface before concrete dimension instantiation. -/
theorem uniform_complete_active_labels_lambda {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f →
      Matrix.det (fun i j => A (f i) j) ≠ 0)
    (v : Fin (d + 1) → K) (hv : v ≠ 0)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (ha : ∀ j, A (label j) ⬝ᵥ v = 0) :
    ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Set.range label :=
  uniform_complete_active_labels A hu v hv label hl ha

#print axioms second_product_real_label_iff
#print axioms uniform_complete_active_labels
end
end ADKZPricing
