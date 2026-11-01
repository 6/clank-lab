import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace BLSH
noncomputable def complete : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], d+1 => 0
  | a::as, d => ∑ k ∈ Finset.range (d+1), a^k * complete as (d-k)
end BLSH

namespace BLSH
/-- Names the requested kernel proposition; never an axiom. -/
def KernelEndpoint : Prop :=
  ∀ m d : Nat, ConvexOn Real {w : Fin m → Real | ∀ i, 0 ≤ w i}
    (fun w => complete (List.ofFn w) d)
end BLSH
