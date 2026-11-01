import Mathlib

namespace BBPSplitStar
open Polynomial

def complementPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  { (0,1), (0,3), (1,2), (2,3) } ∪
    ((Finset.range n).filter (fun j => 5 ≤ j)).image (fun j => (4,j))

def candidatePairs : Finset (ℕ × ℕ) :=
  {(0,1), (0,3), (1,2), (2,3), (4,5), (4,6), (4,7), (8,9), (8,10), (8,11)}

def graphFromComplement (n : ℕ) (E : Finset (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => u ≠ v ∧
    (min u.val v.val, max u.val v.val) ∉ E)

def candidate : SimpleGraph (Fin 12) := graphFromComplement 12 candidatePairs
def J (n : ℕ) : SimpleGraph (Fin n) := graphFromComplement n (complementPairs n)

noncomputable def A {n : ℕ} (G : SimpleGraph (Fin n)) : Polynomial ℤ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    if (G.induce (↑S : Set (Fin n))).IsAcyclic then X ^ S.card else 0

noncomputable def expectedCandidate : Polynomial ℤ := X^4 + 90*X^3 + 66*X^2 + 12*X + 1
noncomputable def expectedComparator : Polynomial ℤ := X^4 + 85*X^3 + 66*X^2 + 12*X + 1
noncomputable def evalR (p : Polynomial ℤ) (x : ℝ) : ℝ :=
  (p.map (Int.castRingHom ℝ)).eval x
noncomputable def evalC (p : Polynomial ℤ) (z : ℂ) : ℂ :=
  (p.map (Int.castRingHom ℂ)).eval z

def UniversalRealAssertion : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∃ ρ : ℝ, evalR (A (J n)) ρ = 0 ∧
    ∀ G : SimpleGraph (Fin n), A G ≠ A (J n) →
      ∀ r : ℝ, evalR (A G) r = 0 → ρ < r

def UniversalModulusAssertion : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∃ ζ : ℂ, evalC (A (J n)) ζ = 0 ∧
    ∀ G : SimpleGraph (Fin n), ∀ z : ℂ,
      evalC (A G) z = 0 → ‖z‖ ≤ ‖ζ‖

def Endpoint : Prop :=
  A candidate = expectedCandidate ∧
  A (J 12) = expectedComparator ∧
  (∃ r : ℝ, -100 < r ∧ r < -86 ∧ evalR (A candidate) r = 0) ∧
  (∀ z : ℂ, evalC (A (J 12)) z = 0 → ‖z‖ < 86) ∧
  A candidate ≠ A (J 12) ∧
  ¬ UniversalRealAssertion ∧ ¬ UniversalModulusAssertion

end BBPSplitStar
