import StanleySnf.Final
import StanleySnf.Fidelity

/-! Exact statement, small values, and permitted axioms checked by the default build. -/

namespace StanleySnf

example : ∀ (n : ℕ), 0 < n →
    HasStanleySNF n (M n) ∧ (∀ r, r + 1 < n → stanleyD n r ∣ stanleyD n (r + 1)) :=
  stanley_class_sum_snf

example : (List.range 1).map (stanleyD 1) = [1] := by decide
example : (List.range 2).map (stanleyD 2) = [1, 1] := by decide
example : (List.range 3).map (stanleyD 3) = [1, 2, 2] := by decide
example : (List.range 4).map (stanleyD 4) = [1, 1, 2, 6] := by decide
example : (List.range 5).map (stanleyD 5) = [1, 2, 2, 12, 24] := by decide
example : (List.range 6).map (stanleyD 6) = [1, 1, 2, 2, 24, 120] := by decide
example : (List.range 7).map (stanleyD 7) = [1, 2, 2, 12, 24, 240, 720] := by decide
example : (List.range 8).map (stanleyD 8) = [1, 1, 2, 6, 12, 120, 720, 5040] := by decide
example : (List.range 9).map (stanleyD 9) =
    [1, 2, 2, 4, 24, 240, 240, 10080, 40320] := by decide
example : (List.range 10).map (stanleyD 10) =
    [1, 1, 2, 6, 24, 24, 720, 5040, 40320, 362880] := by decide
example : (List.range 12).map (stanleyD 12) =
    [1, 1, 2, 2, 12, 120, 240, 5040, 20160, 120960, 3628800, 39916800] := by decide

end StanleySnf

/-- info: 'StanleySnf.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.main

/-- info: 'StanleySnf.bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.bridge

/-- info: 'StanleySnf.stanley_class_sum_snf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.stanley_class_sum_snf

/-- info: 'StanleySnf.Fid.classSum_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.Fid.classSum_coeff

/-- info: 'StanleySnf.Fid.rep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.Fid.rep_spec

/-- info: 'StanleySnf.Fid.parts_eq_iff_isConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.Fid.parts_eq_iff_isConj

/-- info: 'StanleySnf.Fid.M_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySnf.Fid.M_structure
