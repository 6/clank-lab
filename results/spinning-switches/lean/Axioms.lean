import SpinningSwitches

/-! Axiom guards: the main results use only the standard axioms. -/

/-- info: 'SpinningSwitches.classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SpinningSwitches.classification

/-- info: 'SpinningSwitches.S3_wr_C2_unsolvable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SpinningSwitches.S3_wr_C2_unsolvable

/-- info: 'SpinningSwitches.A4_wr_C3_unsolvable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SpinningSwitches.A4_wr_C3_unsolvable
