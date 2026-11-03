import Statement
import UniformCount

/-! The build fails if a main theorem depends on axioms beyond the standard three. -/

/-- info: 'GreedyLPHittingSet.leftmost_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GreedyLPHittingSet.leftmost_explicit

/-- info: 'ADG.full_frozen_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADG.full_frozen_endpoint

/-- info: 'ADG.Uniform.full_uniform_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADG.Uniform.full_uniform_endpoint

/-- info: 'ADG.Uniform.countProb_good_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADG.Uniform.countProb_good_ceiling
