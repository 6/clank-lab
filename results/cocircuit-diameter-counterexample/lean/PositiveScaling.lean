import ProductCells

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def rowScaled {R : Type*} [Mul R] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) R) (scale : Fin n → R) : Matrix (Fin n) (Fin r) R :=
  fun i j => scale i * A i j

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem rowScaled_value {n r : ℕ} (A : Matrix (Fin n) (Fin r) 𝕜)
    (scale : Fin n → 𝕜) (v : Fin r → 𝕜) (i : Fin n) :
    rowScaled A scale i ⬝ᵥ v = scale i * (A i ⬝ᵥ v) := by
  simp only [rowScaled, dotProduct, mul_assoc, ← Finset.mul_sum]

/-- Positive denominator clearing preserves every signed closed cell and
    every zero label in both directions, not only a chosen list of points. -/
theorem rowScaled_signed_slacks {n r : ℕ} (A : Matrix (Fin n) (Fin r) 𝕜)
    (scale : Fin n → 𝕜) (hs : ∀ i, 0 < scale i) (signs : Fin n → 𝕜)
    (v : Fin r → 𝕜) (i : Fin n) :
    (0 ≤ signs i * (rowScaled A scale i ⬝ᵥ v) ↔ 0 ≤ signs i * (A i ⬝ᵥ v)) ∧
    (rowScaled A scale i ⬝ᵥ v = 0 ↔ A i ⬝ᵥ v = 0) := by
  rw [rowScaled_value]
  constructor
  · rw [mul_left_comm]
    exact mul_nonneg_iff_of_pos_left (hs i)
  · exact mul_eq_zero_iff_left (hs i).ne'

theorem rowScaled_star_iff {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (scale : Fin n → 𝕜) (hs : ∀ i, 0 < scale i)
    (cell : Option (Fin n)) (v : Fin (d + 1) → 𝕜) :
    StarFeasible (rowScaled A scale) cell v ↔ StarFeasible A cell v := by
  apply forall_congr'
  intro i
  exact (rowScaled_signed_slacks A scale hs (starSign cell) v i).1

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Uniformity survives arbitrary nonzero row scalings. A generic rank
    statement avoids unfolding concrete 41-by-41 determinants. -/
theorem rowScaled_uniform {n r : ℕ} (A : Matrix (Fin n) (Fin r) 𝕜)
    (scale : Fin n → 𝕜) (hs : ∀ i, scale i ≠ 0)
    (hu : ∀ f : Fin r → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0) :
    ∀ f : Fin r → Fin n, Function.Injective f →
      ((rowScaled A scale).submatrix f id).det ≠ 0 := by
  intro f hf
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hu f hf)))
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply hinj
  ext i
  have h := congrFun hxy i
  change rowScaled A scale (f i) ⬝ᵥ x = rowScaled A scale (f i) ⬝ᵥ y at h
  rw [rowScaled_value, rowScaled_value] at h
  exact mul_left_cancel₀ (hs (f i)) h

theorem rowScaled_strict_chart {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (scale : Fin n → 𝕜) (hs : ∀ i, 0 < scale i)
    (hc : ∀ c v, StarFeasible A c v → v ≠ 0 → 0 < v 0) :
    ∀ c v, StarFeasible (rowScaled A scale) c v → v ≠ 0 → 0 < v 0 := by
  intro c v hv hn
  exact hc c v ((rowScaled_star_iff A scale hs c v).mp hv) hn

/-- Exact field embeddings commute with the concrete product matrix,
    retaining both factor label maps and the common chart column. -/
theorem orderedProduct_map {R S : Type*} [CommRing R] [CommRing S]
    {n m d e : ℕ} (φ : R →+* S)
    (A : Matrix (Fin n) (Fin (d + 1)) R)
    (B : Matrix (Fin m) (Fin (e + 1)) R) :
    (orderedProduct A B).map φ = orderedProduct (A.map φ) (B.map φ) := by
  ext i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    refine Fin.cases ?_ (fun l => ?_) j
  · simp [orderedProduct, Matrix.map_apply]
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) l <;>
      simp [orderedProduct, Matrix.map_apply]
  · simp [orderedProduct, Matrix.map_apply]
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) l <;>
      simp [orderedProduct, Matrix.map_apply]

#print axioms rowScaled_signed_slacks
#print axioms rowScaled_uniform
#print axioms rowScaled_strict_chart
#print axioms orderedProduct_map
end
end ADKZPricing
