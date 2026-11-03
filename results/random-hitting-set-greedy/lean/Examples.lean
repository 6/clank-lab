import Statement
import UniformCount

/-! Small examples on explicit matrices. -/
open ADG

-- One isolated path {0,1,2}, {2,3,4}, {4,5,6}, middle first, then every two-row
-- column: leftmost Greedy takes the middle and two pairs (3 columns); the two
-- ends and one pair also cover (3 columns).
example : G onePathControl = 3 := one_path_greedy_control
example : onePathCover.card = 3 ∧ coversBy onePathControl onePathCover := one_path_cover_control

-- Two disjoint isolated paths: Greedy uses 6 columns, the ends and one pair 5,
-- so the LP value is at most 5.
example : G twoPathControl = 6 := two_path_greedy_control
example : twoPathCover.card = 5 ∧ coversBy twoPathControl twoPathCover := two_path_cover_control
example : L twoPathControl ≤ 5 := by
  have h := lp_le_cover twoPathControl twoPathCover two_path_cover_control.2
  rw [two_path_cover_control.1] at h
  exact_mod_cast h

-- Both control matrices lie in the good event: columns of at most three rows and
-- every two-row column present.
example : noLargeColumns twoPathControl ∧ allExactPairs twoPathControl := two_path_good_control

-- Ties go to the leftmost column.
def tieMatrix : ADG.Matrix 2 2 := fun _ => {0, 1}
example : greedyTrace tieMatrix = [(0, 2)] := by decide
