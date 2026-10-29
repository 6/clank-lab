import LabelTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜]

def chartCoordinates {d : ℕ} (h v : Fin (d + 1) → 𝕜) : Fin (d + 1) → 𝕜 :=
  Fin.cons (h ⬝ᵥ v) (fun j => v j.succ)

def chartCoordinatesInv {d : ℕ} (h u : Fin (d + 1) → 𝕜) : Fin (d + 1) → 𝕜 :=
  Fin.cons ((u 0 - ∑ j : Fin d, h j.succ * u j.succ) / h 0) (fun j => u j.succ)

theorem chartCoordinates_left_inverse {d : ℕ} (h : Fin (d + 1) → 𝕜) (hh : h 0 ≠ 0)
    (v : Fin (d + 1) → 𝕜) : chartCoordinatesInv h (chartCoordinates h v) = v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [chartCoordinatesInv, chartCoordinates, Fin.cons_zero, Fin.cons_succ,
      dotProduct, Fin.sum_univ_succ]
    field_simp
  · simp [chartCoordinatesInv, chartCoordinates]

theorem chartCoordinates_right_inverse {d : ℕ} (h : Fin (d + 1) → 𝕜) (hh : h 0 ≠ 0)
    (u : Fin (d + 1) → 𝕜) : chartCoordinates h (chartCoordinatesInv h u) = u := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [chartCoordinates, chartCoordinatesInv, Fin.cons_zero, Fin.cons_succ,
      dotProduct, Fin.sum_univ_succ]
    field_simp
  · simp [chartCoordinatesInv, chartCoordinates]

/-- This rebasing uses only ring operations on the input rows and chart:
    integer inputs stay integer. A positive h[0] preserves every row sign. -/
def chartRebased {R : Type*} [CommRing R] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) R)
    (h : Fin (d + 1) → R) : Matrix (Fin n) (Fin (d + 1)) R :=
  fun i => Fin.cons (A i 0) (fun j => h 0 * A i j.succ - A i 0 * h j.succ)

theorem chartRebased_value {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (h v : Fin (d + 1) → 𝕜) (i : Fin n) :
    chartRebased A h i ⬝ᵥ chartCoordinates h v = h 0 * (A i ⬝ᵥ v) := by
  simp only [chartRebased, chartCoordinates, dotProduct, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
  ring

theorem chartRebased_value_inv {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (h u : Fin (d + 1) → 𝕜) (hh : h 0 ≠ 0) (i : Fin n) :
    chartRebased A h i ⬝ᵥ u = h 0 * (A i ⬝ᵥ chartCoordinatesInv h u) := by
  have he := chartRebased_value A h (chartCoordinatesInv h u) i
  rw [chartCoordinates_right_inverse h hh u] at he
  exact he

/-- Uniformity survives the exact common-chart change, for all row
    subsets simultaneously and with the original row labels unchanged. -/
theorem chartRebased_uniform {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (h : Fin (d + 1) → 𝕜) (hh : h 0 ≠ 0)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0) :
    ∀ f : Fin (d + 1) → Fin n, Function.Injective f → ((chartRebased A h).submatrix f id).det ≠ 0 := by
  intro f hf
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hu f hf)))
  have hnew : Function.Injective ((chartRebased A h).submatrix f id).mulVec := by
    intro u v huv
    have hold : (A.submatrix f id).mulVec (chartCoordinatesInv h u) =
        (A.submatrix f id).mulVec (chartCoordinatesInv h v) := by
      ext i
      have he := congrArg (fun z : Fin (d + 1) → 𝕜 => z i) huv
      change chartRebased A h (f i) ⬝ᵥ u = chartRebased A h (f i) ⬝ᵥ v at he
      rw [chartRebased_value_inv A h u hh, chartRebased_value_inv A h v hh] at he
      exact mul_left_cancel₀ hh he
    have he := congrArg (chartCoordinates h) (hinj hold)
    simpa only [chartCoordinates_right_inverse h hh] using he
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hnew))

/-- Feasibility and the complete original zero-label set are transported
    in both directions. Positivity is required, not merely invertibility. -/
theorem chartRebased_signed_slacks [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (h v : Fin (d + 1) → 𝕜) (hh : 0 < h 0) (s : Fin n → 𝕜) :
    (∀ i, 0 ≤ s i * (chartRebased A h i ⬝ᵥ chartCoordinates h v) ↔ 0 ≤ s i * (A i ⬝ᵥ v)) ∧
    (∀ i, chartRebased A h i ⬝ᵥ chartCoordinates h v = 0 ↔ A i ⬝ᵥ v = 0) := by
  constructor
  · intro i
    rw [chartRebased_value]
    have he : s i * (h 0 * (A i ⬝ᵥ v)) = h 0 * (s i * (A i ⬝ᵥ v)) := by ring
    rw [he]
    exact mul_nonneg_iff_of_pos_left hh
  · intro i
    rw [chartRebased_value]
    simp [hh.ne']

/-- Integer/rational/real evaluation commutes with the exact row formula. -/
theorem chartRebased_map {R S : Type*} [CommRing R] [CommRing S] {n d : ℕ}
    (f : R →+* S) (A : Matrix (Fin n) (Fin (d + 1)) R) (h : Fin (d + 1) → R)
    (i : Fin n) (j : Fin (d + 1)) :
    f (chartRebased A h i j) = chartRebased (A.map f) (fun k => f (h k)) i j := by
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [chartRebased]

/-- A positive representation of a chart in origin-strict rows certifies
    the positive pivot required for this orientation-preserving change. -/
theorem positive_chart_first_coordinate [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜) (h : Fin (d + 1) → 𝕜)
    (l : Fin n → 𝕜) (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (hl : ∀ i, 0 < l i)
    (he : h 0 = ∑ i, l i * A i 0) : 0 < h 0 := by
  rw [he]
  exact Finset.sum_pos (fun i _ => mul_pos (hl i) (ha i)) ⟨i₀, mem_univ _⟩

/-- The SAME strict common chart becomes coordinate zero in every cell.
    The inverse transformation and the nonzero-ray obligation are explicit. -/
theorem chartRebased_strict_chart [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (h : Fin (d + 1) → 𝕜) (hh : 0 < h 0) (s : Fin n → 𝕜)
    (hstrict : ∀ v : Fin (d + 1) → 𝕜, v ≠ 0 →
      (∀ i, 0 ≤ s i * (A i ⬝ᵥ v)) → 0 < h ⬝ᵥ v)
    (u : Fin (d + 1) → 𝕜) (hu : u ≠ 0)
    (hfeas : ∀ i, 0 ≤ s i * (chartRebased A h i ⬝ᵥ u)) : 0 < u 0 := by
  have hn : chartCoordinatesInv h u ≠ 0 := by
    intro hz
    have he := chartCoordinates_right_inverse h hh.ne' u
    rw [hz] at he
    have hzero : chartCoordinates h 0 = 0 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chartCoordinates]
    rw [hzero] at he
    exact hu he.symm
  have hf : ∀ i, 0 ≤ s i * (A i ⬝ᵥ chartCoordinatesInv h u) := by
    intro i
    have hi := hfeas i
    rw [chartRebased_value_inv A h u hh.ne'] at hi
    have he : s i * (h 0 * (A i ⬝ᵥ chartCoordinatesInv h u)) =
        h 0 * (s i * (A i ⬝ᵥ chartCoordinatesInv h u)) := by ring
    rw [he] at hi
    exact nonneg_of_mul_nonneg_right hi hh
  have hp := hstrict _ hn hf
  have he := congrArg (fun v : Fin (d + 1) → 𝕜 => v 0)
    (chartCoordinates_right_inverse h hh.ne' u)
  change h ⬝ᵥ chartCoordinatesInv h u = u 0 at he
  simpa only [he] using hp

#print axioms chartRebased_map
#print axioms positive_chart_first_coordinate
#print axioms chartRebased_strict_chart
#print axioms chartCoordinates_left_inverse
#print axioms chartCoordinates_right_inverse
#print axioms chartRebased_value
#print axioms chartRebased_uniform
#print axioms chartRebased_signed_slacks
end
end ADKZPricing
