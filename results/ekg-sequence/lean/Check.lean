import Statement
import SolutionEndpoint
import ControlEndpoint
import CorollaryStatements
import SolutionSign
import SolutionDensity
import SolutionCycles

-- This type check fixes the public statement independently of the proof text.
example : EndpointStatement := ekg_sharp_all_index

/-- info: 'ekg_sharp_all_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_sharp_all_index
/-- info: 'ekg_pnt_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_pnt_compatibility
/-- info: 'ekg_part_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_part_a
/-- info: 'ekg_part_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_part_b
/-- info: 'ekg_exact_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_exact_counting
/-- info: 'ekg_weak_pnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_weak_pnt
/-- info: 'ekg_endpoint_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_endpoint_control

-- The consequences, checked against their independently fixed statements.
example : EventualSignStatement := ekg_eventual_sign
example : OrdowskiDensityStatement := ekg_ordowski_density
example : BelowDiagonalCountStatement := ekg_below_diagonal_count
example : JasinskiFinitenessStatement := ekg_jasinski_finite
example : ShortCyclesStatement := ekg_short_cycles_finite
example : ExceptionalFinitenessStatement := ekg_exceptional_finite
example : A155549FinitenessStatement := ekg_a155549_finite

/-- info: 'ekg_eventual_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_eventual_sign
/-- info: 'ekg_ordowski_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_ordowski_density
/-- info: 'ekg_below_diagonal_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_below_diagonal_count
/-- info: 'ekg_jasinski_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_jasinski_finite
/-- info: 'ekg_short_cycles_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_short_cycles_finite
/-- info: 'ekg_exceptional_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_exceptional_finite
/-- info: 'ekg_a155549_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ekg_a155549_finite
