import Controls

namespace LitOnlySigma

-- Check the expanded endpoint and the direct negation of the conjecture.
example : Undirected graph ∧ Connected graph ∧
    regularMinimum graph start = 0 ∧ litOnlyMinimum graph start = 4 ∧
    (∀ m, ¬ CompleteMultipartite graph m) ∧ ¬ Conjecture5 graph :=
  counterexample

example : ¬ Conjecture5 graph := not_conjecture5

example : 4 ≤ discrepancy graph ∧ 7 < 2 * discrepancy graph :=
  ⟨discrepancy_at_least_four, exceeds_half⟩

end LitOnlySigma
