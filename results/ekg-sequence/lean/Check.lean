import Statement
import SolutionEndpoint
import ControlEndpoint

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
