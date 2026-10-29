import SourceCover

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem nonsingular_basis_transfer {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) 𝕜) (old new : Fin d → Fin n)
    (ho : (A.submatrix old id).det ≠ 0)
    (hc : ∀ i, ∃ j, old i = new j) : (A.submatrix new id).det ≠ 0 := by
  have hoinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ho))
  have hnew : Function.Injective (A.submatrix new id).mulVec := by
    intro x y hxy
    apply hoinj
    ext i
    obtain ⟨j, hj⟩ := hc i
    have h := congrArg (fun z : Fin d → 𝕜 => z j) hxy
    change A (old i) ⬝ᵥ x = A (old i) ⬝ᵥ y
    rw [hj]
    exact h
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hnew))

/-- The finite source certificate discharges regularity for ANY ordering
    of any feasible d-row label, not merely the certificate's own bases. -/
theorem certified_ordered_affine_regularity {n d : ℕ} {V : Type*}
    [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜) (p : V → Fin d → 𝕜)
    (bas : V → Fin d → Fin n) (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A b (p v))
    (hcount : ∀ v, (activeRows A b (p v)).card = d)
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = b (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (x : Fin d → 𝕜) (hx : AffineFeasible A b x)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (hlx : ∀ j, A (label j) ⬝ᵥ x = b (label j)) :
    (A.submatrix label id).det ≠ 0 ∧
      (∀ i, i ∉ Set.range label → b i < A i ⬝ᵥ x) := by
  classical
  let J := univ.image label
  have hJ : J.card = d := by simp [J, Finset.card_image_of_injective _ hl]
  have hsub : J ⊆ activeRows A b x := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_univ _, hlx j⟩
  obtain ⟨v, hv, hc⟩ := certified_list_covers_many_active A b p bas next gain
    hvertices hcount hgain hactive hinverse x hx (by
      simpa only [hJ] using card_le_card hsub)
  have heq : J = activeRows A b x := eq_of_subset_of_card_le hsub (by omega)
  constructor
  · apply nonsingular_basis_transfer A (bas v) label
      (certified_basis_independent A (bas v) _ (hinverse v))
    intro j
    have hm : bas v j ∈ activeRows A b x := by
      apply mem_filter.mpr
      exact ⟨mem_univ _, by rw [hv]; exact hactive v j⟩
    rw [← heq] at hm
    obtain ⟨k, _, hk⟩ := mem_image.mp hm
    exact ⟨k, hk.symm⟩
  · intro i hi
    apply lt_of_le_of_ne (hx i)
    intro he
    have hm : i ∈ activeRows A b x := mem_filter.mpr ⟨mem_univ _, he.symm⟩
    rw [← heq] at hm
    exact hi (by simpa [J] using hm)

/-- Ordered-label regularity in homogeneous coordinates follows from
    the finite source certificate and positive origin slacks. The strict
    chart is proved here, rather than supplied as a regularity assumption. -/
theorem certified_ordered_homogeneous_regularity {n d : ℕ} {V : Type*}
    [Fintype V] [Nonempty V]
    (a : Fin n → 𝕜) (A : Matrix (Fin n) (Fin d) 𝕜) (i₀ : Fin n)
    (ha : ∀ i, 0 < a i) (p : V → Fin d → 𝕜)
    (bas : V → Fin d → Fin n) (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A (fun i => -a i) (p v))
    (hcount : ∀ v, (activeRows A (fun i => -a i) (p v)).card = d)
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = -a (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (t : 𝕜) (y : Fin d → 𝕜) (hne : t ≠ 0 ∨ y ≠ 0)
    (hcone : ∀ i, 0 ≤ a i * t + A i ⬝ᵥ y)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (hlx : ∀ j, a (label j) * t + A (label j) ⬝ᵥ y = 0) :
    0 < t ∧ (A.submatrix label id).det ≠ 0 ∧
      (∀ i, i ∉ Set.range label → 0 < a i * t + A i ⬝ᵥ y) := by
  have hmax := certified_list_maximizes A (fun i => -a i) p bas next gain hgain hactive hinverse
  have hrec := no_recession_of_maximizers A (fun i => -a i) p hvertices hmax
  have ht := strict_source_chart a A i₀ ha hrec t y hne hcone
  have hnorm := affine_normalization a A t ht y hcone
  have hr := certified_ordered_affine_regularity A (fun i => -a i) p bas next gain
    hvertices hcount hgain hactive hinverse (fun j => y j / t) hnorm.1 label hl
    (fun j => (hnorm.2 (label j)).mp (hlx j))
  refine ⟨ht, hr.1, ?_⟩
  intro i hi
  have hs := hr.2 i hi
  have he : A i ⬝ᵥ (fun j => y j / t) = (A i ⬝ᵥ y) / t := by
    simp only [dotProduct, ← mul_div_assoc, ← Finset.sum_div]
  rw [he, lt_div_iff₀ ht] at hs
  dsimp only at hs
  rw [neg_mul] at hs
  linarith

#print axioms certified_ordered_homogeneous_regularity
#print axioms nonsingular_basis_transfer
#print axioms certified_ordered_affine_regularity
end
end ADKZPricing
