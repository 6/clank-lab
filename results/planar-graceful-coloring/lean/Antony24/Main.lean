import Antony24.Forward
import Antony24.Reverse
import Antony24.Union
import Antony24.MatchingCut
import Antony24.Properties

/-! The main statements, for every finite cubic graph.
No source hardness or complexity result is assumed by these theorems. -/
namespace Antony24

/-- Every finite simple cubic graph, including the empty graph. -/
theorem graceful4_s2_iff_pmc {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : Cubic G) : Graceful4 (S2 G) ↔ PMC G :=
  ⟨graceful4_s2_implies_pmc hG, pmc_implies_graceful4_s2 hG⟩

/-- Fully expanded conventional endpoint: labels 1 through 4, versus an
actual perfect matching equal to the entire subset cut. -/
theorem four_labels_s2_iff_perfectMatching_equal_cut
    {V : Type*} [Finite V] (G : SimpleGraph V) (hG : Cubic G) :
    (∃ c : SubVertex G → ℕ, IsGracefulFourLabels (S2 G) c) ↔
      ∃ (A : Set V) (M : G.Subgraph), M.IsPerfectMatching ∧
        ∀ u v, M.Adj u v ↔ G.Adj u v ∧
          ((u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A)) := by
  exact (graceful4_iff_four_labels (S2 G)).symm.trans
    ((graceful4_s2_iff_pmc G hG).trans (pmc_iff_perfectMatching_equal_cut G))

end Antony24
