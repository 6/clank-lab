import SourceCover

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def affineSegment {d : ℕ} (p q : Fin d → 𝕜) (t : 𝕜) : Fin d → 𝕜 :=
  fun j => (1 - t) * p j + t * q j

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem affineSegment_value {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜)
    (p q : Fin d → 𝕜) (t : 𝕜) (i : Fin n) :
    A i ⬝ᵥ affineSegment p q t = (1 - t) * (A i ⬝ᵥ p) + t * (A i ⬝ᵥ q) := by
  simp only [affineSegment, dotProduct, mul_add, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- One omitted active row parametrizes the entire affine common face.
    This uses actual row equations and a nonsingular spatial basis. -/
theorem one_row_face_parameter {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜)
    (b : Fin n → 𝕜) (p q : Fin d → 𝕜) (bas : Fin d → Fin n) (drop : Fin d)
    (hdet : (A.submatrix bas id).det ≠ 0)
    (hp : ∀ j, A (bas j) ⬝ᵥ p = b (bas j))
    (hq : ∀ j, j ≠ drop → A (bas j) ⬝ᵥ q = b (bas j))
    (hg : 0 < A (bas drop) ⬝ᵥ q - b (bas drop))
    (x : Fin d → 𝕜) (hx : ∀ j, j ≠ drop → A (bas j) ⬝ᵥ x = b (bas j)) :
    x = affineSegment p q
      ((A (bas drop) ⬝ᵥ x - b (bas drop)) / (A (bas drop) ⬝ᵥ q - b (bas drop))) := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  ext j
  change A (bas j) ⬝ᵥ x = A (bas j) ⬝ᵥ affineSegment p q _
  rw [affineSegment_value, hp]
  by_cases hj : j = drop
  · subst j
    field_simp
    nlinarith [hg.ne']
  · rw [hq j hj, hx j hj]
    ring

/-- The geometric common face of two certified neighbors is exactly their
    closed segment. A newly tight ORIGINAL row bounds its other end.
    Thus local ridge pairing certifies edges, not merely abstract adjacency. -/
theorem certified_common_face_segment {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜)
    (b : Fin n → 𝕜) (p q : Fin d → 𝕜) (bas : Fin d → Fin n) (drop : Fin d)
    (hdet : (A.submatrix bas id).det ≠ 0)
    (hpfeas : AffineFeasible A b p) (hqfeas : AffineFeasible A b q)
    (hp : ∀ j, A (bas j) ⬝ᵥ p = b (bas j))
    (hq : ∀ j, j ≠ drop → A (bas j) ⬝ᵥ q = b (bas j))
    (hg : 0 < A (bas drop) ⬝ᵥ q - b (bas drop))
    (newRow : Fin n) (hnew : A newRow ⬝ᵥ q = b newRow)
    (hstrict : b newRow < A newRow ⬝ᵥ p) (x : Fin d → 𝕜) :
    (AffineFeasible A b x ∧ ∀ j, j ≠ drop → A (bas j) ⬝ᵥ x = b (bas j)) ↔
      ∃ t : 𝕜, 0 ≤ t ∧ t ≤ 1 ∧ x = affineSegment p q t := by
  constructor
  · rintro ⟨hxf, hxa⟩
    let t := (A (bas drop) ⬝ᵥ x - b (bas drop)) / (A (bas drop) ⬝ᵥ q - b (bas drop))
    have he := one_row_face_parameter A b p q bas drop hdet hp hq hg x hxa
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hxf (bas drop))) hg.le
    have hupper : t ≤ 1 := by
      have h := hxf newRow
      rw [he, affineSegment_value, hnew] at h
      change b newRow ≤ (1 - t) * (A newRow ⬝ᵥ p) + t * b newRow at h
      nlinarith
    exact ⟨t, ht, hupper, he⟩
  · rintro ⟨t, ht, ht1, rfl⟩
    constructor
    · intro i
      rw [affineSegment_value]
      have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hpfeas i))
      have h2 := mul_nonneg ht (sub_nonneg.mpr (hqfeas i))
      nlinarith
    · intro j hj
      rw [affineSegment_value, hp, hq j hj]
      ring

/-- Every original row vanishes at an interior edge point exactly when
    it vanishes at both endpoints. No facet labels are deleted or merged. -/
theorem segment_interior_active_iff {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜)
    (b : Fin n → 𝕜) (p q : Fin d → 𝕜)
    (hp : AffineFeasible A b p) (hq : AffineFeasible A b q)
    (t : 𝕜) (ht : 0 < t) (ht1 : t < 1) (i : Fin n) :
    A i ⬝ᵥ affineSegment p q t = b i ↔
      A i ⬝ᵥ p = b i ∧ A i ⬝ᵥ q = b i := by
  rw [affineSegment_value]
  constructor
  · intro h
    have h1 := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hp i))
    have h2 := mul_nonneg ht.le (sub_nonneg.mpr (hq i))
    have hz1 : (1 - t) * (A i ⬝ᵥ p - b i) = 0 := by nlinarith
    have hz2 : t * (A i ⬝ᵥ q - b i) = 0 := by nlinarith
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hz1).resolve_left (sub_pos.mpr ht1).ne'),
      sub_eq_zero.mp ((mul_eq_zero.mp hz2).resolve_left ht.ne')⟩
  · rintro ⟨hp, hq⟩
    rw [hp, hq]
    ring

#print axioms certified_common_face_segment
#print axioms segment_interior_active_iff
end
end ADKZPricing
