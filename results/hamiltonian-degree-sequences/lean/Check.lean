import Main

/-! Checked by `lake build`: the exact statements of the main theorems, and that each
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. -/

namespace NWDigraph

/-- Kühn–Osthus–Treglown's Conjecture 6 fails for every `n ≥ 7`. -/
example : ∀ n ≥ 7, ∃ G : Digraph n, KOTHyp G ∧ ¬ HasHamCycle G :=
  kot_counterexample_all

example : ¬ KOTConjecture6 := not_kotConjecture6

/-- Nash-Williams' conjecture fails for every `n ≥ 6`. -/
example : ∀ n ≥ 6, ∃ G : Digraph n, StronglyConnected G ∧ NWHyp G ∧ ¬ HasHamCycle G :=
  counterexample_all

example : ¬ NashWilliamsConjecture := not_nashWilliamsConjecture

example (u : ℕ) (hu : 4 ≤ u) :
    StronglyConnected (F u) ∧ NWHyp (F u) ∧ ¬ HasHamCycle (F u) :=
  F_counterexample u hu

example : ¬ CycleThrough G6 2 3 := G6_no_cycle_through_2_3

example (u : ℕ) : ¬ CycleThrough (F u) ⟨u, by omega⟩ ⟨u + 2, by omega⟩ :=
  F_no_cycle_through_s_r1 u

example (u : ℕ) : ¬ CycleThrough (F u) ⟨u, by omega⟩ ⟨u + 3, by omega⟩ :=
  F_no_cycle_through_s_r2 u

/-- info: 'NWDigraph.kot_counterexample_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kot_counterexample_all

/-- info: 'NWDigraph.not_kotConjecture6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_kotConjecture6

/-- info: 'NWDigraph.counterexample_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample_all

/-- info: 'NWDigraph.not_nashWilliamsConjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_nashWilliamsConjecture

/-- info: 'NWDigraph.F_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms F_counterexample

/-- info: 'NWDigraph.G6_no_cycle_through_2_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms G6_no_cycle_through_2_3

/-- info: 'NWDigraph.F_no_cycle_through_s_r1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms F_no_cycle_through_s_r1

/-- info: 'NWDigraph.F_no_cycle_through_s_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms F_no_cycle_through_s_r2

end NWDigraph
