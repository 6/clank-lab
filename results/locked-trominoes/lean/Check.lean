import Generated.Universal

/-!
The checked statement, restated from the definitions in `Core.lean`, and its
axioms. `lake build` fails if the theorem's type differs from this one or if
it depends on anything beyond Lean's three standard axioms.
-/

namespace LockedTromino.Check

open LockedTromino

/-- Every `m × n` rectangle with `3 ∣ m`, `m ≥ 6` and `n ≥ 4` has a locked tromino tiling. -/
theorem locked_tromino_tiling_exists :
    ∀ m n : Nat, 6 ≤ m → 3 ∣ m → 4 ≤ n → ∃ T, Locked (Rectangle m n) T :=
  LockedTromino.Witnesses.locked_tromino_rectangles

/--
info: 'LockedTromino.Witnesses.locked_tromino_rectangles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LockedTromino.Witnesses.locked_tromino_rectangles

/-! Small checks of the definitions: cells are (row, column) pairs, adjacency is
sharing a side, and `Rectangle m n` has rows `0, …, m - 1` and columns `0, …, n - 1`. -/

example : Adj (0, 0) (0, 1) := by unfold Adj; decide
example : Adj (2, 3) (1, 3) := by unfold Adj; decide
example : ¬ Adj (0, 0) (1, 1) := by unfold Adj; decide
example : ¬ Adj (0, 0) (0, 2) := by unfold Adj; decide
example : Rectangle 6 4 (5, 3) := by unfold Rectangle; decide
example : ¬ Rectangle 6 4 (6, 0) := by unfold Rectangle; decide
example : ¬ Rectangle 6 4 (0, 4) := by unfold Rectangle; decide

end LockedTromino.Check
