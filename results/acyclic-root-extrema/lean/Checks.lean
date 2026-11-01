import Final

example : BBPSplitStar.Endpoint := BBPSplitStar.endpoint

example : BBPSplitStar.candidatePairs.card = 10 := by decide
example : (BBPSplitStar.complementPairs 12).card = 11 := by decide
example : (0, 2) ∉ BBPSplitStar.candidatePairs := by decide
example : (0, 1) ∈ BBPSplitStar.candidatePairs := by decide

/-- info: 'BBPSplitStar.candidate_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BBPSplitStar.candidate_coefficients

/-- info: 'BBPSplitStar.comparator_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BBPSplitStar.comparator_coefficients

/-- info: 'BBPSplitStar.candidate_real_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BBPSplitStar.candidate_real_interval

/-- info: 'BBPSplitStar.comparator_complex_disk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BBPSplitStar.comparator_complex_disk

/-- info: 'BBPSplitStar.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BBPSplitStar.endpoint

