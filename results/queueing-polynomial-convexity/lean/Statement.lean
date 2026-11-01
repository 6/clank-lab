import Final

open BLSUnit1
open scoped BigOperators

-- The public theorem has the original parameter range and the literal tuple sum.
example : ∀ n L d : ℕ, 2 ≤ n → 2 ≤ L → 2 ≤ d →
    ConvexOn ℝ (stdSimplex ℝ (Edge n L)) (sourcePolynomial n L d) :=
  BLSFinal.fullEndpoint

example {n L : ℕ} (hL : 1 ≤ L) (d : ℕ) :
    ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e}
      (sourcePolynomial n L d) := BLSFinal.source_orthant hL d

example (n L d : ℕ) (x : Edge n L → ℝ) :
    sourcePolynomial n L d x =
      ∑ s : Fin d → Edge n L, ∏ i : Fin d,
        x (s i) / (((Finset.univ : Finset (Fin d)).filter
          (fun j => j.val ≤ i.val)).biUnion (fun j => (s j).val)).card := rfl

example (n L : ℕ) :
    stdSimplex ℝ (Edge n L) = {x | (∀ e, 0 ≤ x e) ∧ ∑ e, x e = 1} := rfl

example (n L : ℕ) (e : Finset (Fin n)) :
    e ∈ (Finset.univ : Finset (Fin n)).powersetCard L ↔ e.card = L := by
  simp [Finset.mem_powersetCard]
