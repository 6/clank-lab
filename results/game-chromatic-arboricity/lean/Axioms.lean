import Main

/-!
Axiom guards. The cited theorem is the hypothesis `hC4 : GCG.C4FreeSubgraphTheorem` of
both final theorems, not an `axiom`, so these guards fail on any axiom beyond the three
standard ones and on `sorryAx`.
-/

/-- info: 'GCG.exists_subgraph_bob_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GCG.exists_subgraph_bob_wins

/-- info: 'GCG.bounded_arboricity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GCG.bounded_arboricity

/-- info: 'GCG.bob_wins_of_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GCG.bob_wins_of_structure
