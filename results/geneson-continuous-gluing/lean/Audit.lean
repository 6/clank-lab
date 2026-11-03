import SourceBridge
import Controls

open Set

/-- The full statement, with arbitrary planar subsets and inclusive anchor inequalities. -/
example (n : ℝ) (hn : 0 < n) (P Q : Set Geneson.Plane) (c d : ℝ)
    (hp : (c,d) ∈ P) (hq : (c,d) ∈ Q)
    (hP : ∀ p ∈ P, p.1 ≤ c ∧ p.2 ≤ d)
    (hQ : ∀ q ∈ Q, c ≤ q.1 ∧ d ≤ q.2) :
    Geneson.opx n (P ∪ Q) ≤ Geneson.opx n P + Geneson.opx n Q :=
  Geneson.geneson_conjecture_6_3 n hn P Q c d hp hq hP hQ

/-- info: 'Geneson.geneson_conjecture_6_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.geneson_conjecture_6_3

/-- info: 'Geneson.contains_iff_hasCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.contains_iff_hasCopy

/-- info: 'Geneson.isCompact_witnessSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.isCompact_witnessSpace

/-- info: 'Geneson.isCompact_anchorSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.isCompact_anchorSet

/-- info: 'Geneson.exists_open_avoiding_superset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.exists_open_avoiding_superset

/-- info: 'Geneson.measurable_avoiding_area_le_opx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geneson.measurable_avoiding_area_le_opx

/-- info: 'SrcCheck.conjecture_6_3_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SrcCheck.conjecture_6_3_source

