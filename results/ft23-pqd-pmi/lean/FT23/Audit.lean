import FT23.Final
import FT23.Control

namespace FT23

-- Check the public theorem's type without a weaker intermediate interface.
example : StrictGenerator phi psi ∧ IsCopula C ∧ PQD C ∧ ¬ PrimaryPMI C :=
  conjecture_counterexample

example : ValidRect ((63 : ℝ)/256) (65/256) (61/768) (67/768) := by
  norm_num [ValidRect]

example (a b d e : ℝ) : delta (E independence) a b d e = 0 :=
  independence_delta a b d e

/-- info: 'FT23.conjecture_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FT23.conjecture_counterexample

/-- info: 'FT23.conjecture_equivalence_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FT23.conjecture_equivalence_false

/-- info: 'FT23.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FT23.endpoint

end FT23
