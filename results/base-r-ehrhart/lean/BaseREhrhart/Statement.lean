import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic

/-! The statement: the simplex, its dilates, their lattice points and the
claimed Ehrhart polynomial.
This file defines the proposition to prove; it does not assert its proof. -/
noncomputable section
open scoped BigOperators
namespace BaseREhrhart

def coefficients : Fin 5 → ℤ := ![13, 182, 2548, 35672, 499408]

def simplexVertex {d : ℕ} (c : Fin d → ℝ) : Fin (d+1) → (Fin d → ℝ) :=
  Fin.cases (fun i => -c i) (fun j i => if i = j then 1 else 0)

def simplex : Set (Fin 5 → ℝ) :=
  convexHull ℝ (Set.range (simplexVertex (fun i => (coefficients i : ℝ))))

/-- Literal scalar image of the actual convex hull, also at zero. -/
def dilate (t : ℕ) : Set (Fin 5 → ℝ) :=
  (fun y : Fin 5 → ℝ => (t : ℝ) • y) '' simplex

def LatticePoints (t : ℕ) := {x : Fin 5 → ℤ // (fun i => (x i : ℝ)) ∈ dilate t}

def proposedPolynomial (t : ℚ) : ℚ :=
  1 - (268/15)*t + (3955/12)*t^2 + (5833/2)*t^3 +
    (10343/12)*t^4 + (67228/15)*t^5

def AllTEhrhartClaim : Prop := ∀ t : ℕ,
  (Nat.card (LatticePoints t) : ℚ) = proposedPolynomial t
end BaseREhrhart
