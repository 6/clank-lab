import LabelTransport
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.EquivFin

namespace ADKZPricing
open Finset Matrix
noncomputable section
variable {𝕜 : Type*} [Field 𝕜]

/-- Global uniformity bounds the zero set at EVERY nonzero vector;
    this is not an inference from a simple cell graph. -/
theorem uniform_zero_count [DecidableEq 𝕜] {n r : ℕ} (A : Matrix (Fin n) (Fin r) 𝕜)
    (hu : ∀ f : Fin r → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (v : Fin r → 𝕜) (hv : v ≠ 0) :
    (univ.filter (fun i => A i ⬝ᵥ v = 0)).card < r := by
  classical
  by_contra hn
  obtain ⟨J, hJ, hc⟩ := exists_subset_card_eq (le_of_not_gt hn)
  let e := (J.equivFinOfCardEq hc).symm
  let f : Fin r → Fin n := fun j => (e j).val
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  let K := A.submatrix f id
  have hk : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr (hu f hf))
  have hz : K.mulVec v = 0 := by
    ext j
    exact (mem_filter.mp (hJ (e j).property)).2
  apply hv
  apply Matrix.mulVec_injective_iff_isUnit.mpr hk
  simpa using hz

/-- Uniformity discharges the nonsingular-completion premise for ANY
    labelled charted active basis, using one unused row, not enumeration. -/
theorem uniform_charted_spatial_basis {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜) (hn : d < n)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (bas : Fin d → Fin n) (hbas : Function.Injective bas)
    (v : Fin (d + 1) → 𝕜) (hv : v 0 = 1)
    (hactive : ∀ i, A (bas i) ⬝ᵥ v = 0) :
    (A.submatrix bas Fin.succ).det ≠ 0 := by
  classical
  have hc : (univ.image bas).card < (univ : Finset (Fin n)).card := by
    simpa [Finset.card_image_of_injective _ hbas] using hn
  obtain ⟨j, _, hj⟩ := exists_mem_not_mem_of_card_lt_card hc
  let f : Fin (d + 1) → Fin n := Fin.cons j bas
  have hf : Function.Injective f := Fin.cons_injective_iff.mpr ⟨by simpa using hj, hbas⟩
  have hk := charted_spatial_minor (A.submatrix f id) (hu f hf) v hv (by
    intro i
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, f] using hactive i)
  simpa [Matrix.submatrix, f] using hk

/-- The two factor projections share the same chart coordinate. If both
    factors have a strict chart, so does their product, including points
    for which one projection might initially be zero. -/
theorem product_strict_chart [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {d e : ℕ} (P : 𝕜 → (Fin d → 𝕜) → Prop) (Q : 𝕜 → (Fin e → 𝕜) → Prop)
    (hP : ∀ t x, P t x → (t ≠ 0 ∨ x ≠ 0) → 0 < t)
    (hQ : ∀ t y, Q t y → (t ≠ 0 ∨ y ≠ 0) → 0 < t)
    (t : 𝕜) (x : Fin d → 𝕜) (y : Fin e → 𝕜)
    (hp : P t x) (hq : Q t y) (hne : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) :
    0 < t ∧ (t ≠ 0 ∨ x ≠ 0) ∧ (t ≠ 0 ∨ y ≠ 0) := by
  have ht : 0 < t := by
    rcases hne with ht | hx | hy
    · exact hP t x hp (Or.inl ht)
    · exact hP t x hp (Or.inr hx)
    · exact hQ t y hq (Or.inr hy)
  exact ⟨ht, Or.inl ht.ne', Or.inl ht.ne'⟩

/-- Counts add with disjoint ORIGINAL row labels. A product vertex has
    the full count in each factor; no product vertices are enumerated. -/
theorem product_active_counts {n m d e : ℕ}
    (I : Finset (Fin n)) (J : Finset (Fin m))
    (hi : I.card ≤ d) (hj : J.card ≤ e)
    (hmany : d + e ≤ (I.disjSum J).card) :
    I.card = d ∧ J.card = e ∧ (I.disjSum J).card = d + e := by
  rw [card_disjSum] at hmany ⊢
  omega

/-- Once the two actual active spatial bases are obtained, their product
    basis is nonsingular by a determinant identity, without minor scans. -/
theorem product_active_basis {d e : ℕ}
    (A : Matrix (Fin d) (Fin d) 𝕜) (B : Matrix (Fin e) (Fin e) 𝕜)
    (ha : A.det ≠ 0) (hb : B.det ≠ 0) :
    (Matrix.fromBlocks A 0 0 B).det ≠ 0 := by
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero ha hb

#print axioms uniform_charted_spatial_basis
#print axioms uniform_zero_count
#print axioms product_strict_chart
#print axioms product_active_counts
#print axioms product_active_basis
end
end ADKZPricing
