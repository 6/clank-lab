import Controls
import ThreeTypes
import UniformBlowup

namespace LitOnlySigma

-- Check the expanded endpoint and the direct negation of the conjecture.
example : Undirected graph ∧ Connected graph ∧
    regularMinimum graph start = 0 ∧ litOnlyMinimum graph start = 4 ∧
    (∀ m, ¬ CompleteMultipartite graph m) ∧ ¬ Conjecture5 graph :=
  counterexample

example : ¬ Conjecture5 graph := not_conjecture5

example : 4 ≤ discrepancy graph ∧ 7 < 2 * discrepancy graph :=
  ⟨discrepancy_at_least_four, exceeds_half⟩

example : ThreeTypeStatement := three_type_description

example : ∀ m : ℕ, 0 < m →
    Undirected (blowup m) ∧ Connected (blowup m) ∧
    (∀ v, blowup m v v = false) ∧
    regularMinimum (blowup m) (uniformStart m) = 0 ∧
    litOnlyMinimum (blowup m) (uniformStart m) = 4 * m ∧
    4 * m ≤ discrepancy (blowup m) ∧ 7 * m < 2 * discrepancy (blowup m) ∧
    (∀ parts, ¬ CompleteMultipartite (blowup m) parts) := uniform_blowup

end LitOnlySigma
