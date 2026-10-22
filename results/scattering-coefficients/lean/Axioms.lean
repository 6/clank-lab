import Main
import Examples
import ErsConj13.Existence

/-! Axiom guards. Each `#guard_msgs` fails the build unless the theorem depends on exactly the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'ErsConj13.ers_conjecture_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.ers_conjecture_13

/-- info: 'ErsConj13.ray21_eq_S5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.ray21_eq_S5

/-- info: 'ErsConj13.main_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.main_lemma

/-- info: 'ErsConj13.transport5_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.transport5_consistent

/-- info: 'ErsConj13.realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.realization

/-- info: 'ErsConj13.Scat.factor_exists_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.Scat.factor_exists_aux

/-- info: 'ErsConj13.Scat.factor_unique_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.Scat.factor_unique_aux

/-- info: 'ErsConj13.S_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.S_cubic

/-- info: 'ErsConj13.exists_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.exists_T

/-- info: 'ErsConj13.exists_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.exists_theta

/-- info: 'ErsConj13.bracket_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ErsConj13.bracket_monomial
