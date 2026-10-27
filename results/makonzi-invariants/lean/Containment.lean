import Endpoint
import Mathlib.Tactic.LinearCombination

namespace Makonzi
open scoped BigOperators

@[simp] theorem arrowEval_W0 (p : Fin 3 → ℕ) :
    arrowEval p (W p 0) = D p 0 * U p 1 := by
  simp [arrowEval, W, arrowImage]

@[simp] theorem arrowEval_W1 (p : Fin 3 → ℕ) :
    arrowEval p (W p 1) = D p 1 * U p 0 := by
  simp [arrowEval, W, arrowImage]

@[simp] theorem arrowEval_W2 (p : Fin 3 → ℕ) :
    arrowEval p (W p 2) = -(D p 1 * U p 2) := by
  simp [arrowEval, W, arrowImage]

@[simp] theorem arrowEval_V (p : Fin 3 → ℕ) (i : Fin 3) :
    arrowEval p (V p i) = D p i * U p i := by
  simp [arrowEval, V, arrowImage, D, U, Finset.prod_mul_distrib]

/-- Source Proposition 5.1's vanishing direction, uniformly, without an
arm-length restriction or any localization/fibre hypothesis. -/
theorem minorIdeal_le_ker (p : Fin 3 → ℕ) :
    minorIdeal p ≤ RingHom.ker (phi p) := by
  let q := Ideal.Quotient.mk (canonicalIdeal p)
  have hrel : q (D p 0) - q (D p 1) + q (D p 2) = 0 := by
    have h : D p 0 - D p 1 + D p 2 ∈ canonicalIdeal p :=
      Ideal.subset_span (Set.mem_singleton _)
    have hq := (Ideal.Quotient.eq_zero_iff_mem).mpr h
    simpa only [map_add, map_sub] using hq
  apply Ideal.span_le.mpr
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · change q (arrowEval p _) = 0
    simp only [map_sub, map_add, map_mul, arrowEval_W1, arrowEval_W2, arrowEval_V,
      map_neg]
    linear_combination (q (D p 1) * q (U p 0) * q (U p 2)) * hrel
  · change q (arrowEval p _) = 0
    simp only [map_sub, map_mul, arrowEval_W1, arrowEval_W0, arrowEval_V]
    ring
  · change q (arrowEval p _) = 0
    simp only [map_sub, map_add, map_mul, arrowEval_W2, arrowEval_W0, arrowEval_V,
      map_neg]
    linear_combination -(q (D p 1) * q (U p 1) * q (U p 2)) * hrel

#print axioms minorIdeal_le_ker
end Makonzi
