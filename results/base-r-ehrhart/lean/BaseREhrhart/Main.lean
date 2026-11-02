import BaseREhrhart.Counting
import BaseREhrhart.Certificate
import BaseREhrhart.Independence
import BaseREhrhart.PolynomialObject

/-! Main theorems.
The final statements count actual integer points in the scalar image of
the convex hull of the six specified integral vertices. No geometric or
finite-certificate premise remains in these statements. -/

noncomputable section
open scoped BigOperators
namespace BaseREhrhart

/-- The exact all-t identity, including t=0, for the literal simplex. -/
theorem allTEhrhart : AllTEhrhartClaim :=
  ehrhart_of_histogram height_histogram

/-- There are finitely many actual lattice points at every natural t. -/
instance latticePointsFinite (t : ℕ) : Finite (LatticePoints t) := by
  let e : Pieces t ≃ (b : Fin D) × Fiber t b :=
    Equiv.subtypeProdEquivSigmaSubtype
      (fun (b : Fin D) (n : Fin 6 → ℕ) => height b + ∑ j, n j = t)
  exact Finite.of_equiv ((b : Fin D) × Fiber t b) ((latticeEquivPieces t).trans e).symm

/-- The geometric counting function is this polynomial at every natural
scale, and its linear coefficient is negative. -/
theorem actual_lattice_count_and_negative_coefficient :
    (∀ t : ℕ, (Nat.card (LatticePoints t) : ℚ) = latticePolynomial.eval (t : ℚ)) ∧
      latticePolynomial.coeff 1 = -268 / 15 ∧ latticePolynomial.coeff 1 < 0 := by
  refine ⟨fun t => (allTEhrhart t).trans (latticePolynomial_eval t).symm, ?_, ?_⟩
  · exact latticePolynomial_linear_coefficient
  · exact latticePolynomial_linear_negative

/-- At scale zero the scalar image contributes the single origin. -/
theorem lattice_count_zero : Nat.card (LatticePoints 0) = 1 := by
  have h := allTEhrhart 0
  norm_num [proposedPolynomial] at h
  exact_mod_cast h

end BaseREhrhart
