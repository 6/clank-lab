import BaseREhrhart.Main

/-! The statement, small checks and axiom guards, built by `lake build`. -/

namespace BaseREhrhart

-- The main theorem has exactly the stated type.
example : AllTEhrhartClaim := allTEhrhart

example : ∀ t : ℕ, (Nat.card (LatticePoints t) : ℚ) =
    1 - (268/15)*t + (3955/12)*t^2 + (5833/2)*t^3 +
      (10343/12)*t^4 + (67228/15)*t^5 :=
  allTEhrhart

-- The fixed vertex is -(r-1)(1, r, ..., r^4) with r = 14, as in the base-r simplex.
example : ∀ i : Fin 5, coefficients i = 13 * 14 ^ (i : ℕ) := by decide

-- The normalized volume r^d = 14^5 is the number of residues.
example : D = 14 ^ 5 := by decide

-- The six heights sum to the normalized volume.
example : ∑ h : Fin 6, weight h = D := by decide

-- The first dilate: the lattice points of the simplex itself.
example : Nat.card (LatticePoints 1) = 8573 := by
  have h := allTEhrhart 1
  norm_num [proposedPolynomial] at h
  exact_mod_cast h

/-- info: 'BaseREhrhart.allTEhrhart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allTEhrhart

/-- info: 'BaseREhrhart.actual_lattice_count_and_negative_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_lattice_count_and_negative_coefficient

/-- info: 'BaseREhrhart.vertices_affineIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vertices_affineIndependent

/-- info: 'BaseREhrhart.lattice_count_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lattice_count_zero

/-- info: 'BaseREhrhart.height_histogram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms height_histogram

/-- info: 'BaseREhrhart.latticeEquivPieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms latticeEquivPieces

end BaseREhrhart
