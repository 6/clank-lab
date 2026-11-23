import Check

/-- There exists a planar graph with 82 vertices, with no simple cycle of
length four or nine and with no proper three-coloring. Planarity is witnessed
by a crossing-free straight-line drawing with rational vertex coordinates. -/
theorem challenge :
    ∃ G : SimpleGraph (Fin 82),
      (∃ draw : Fin 82 → ℚ × ℚ, Steinberg.CrossingFreeDrawing G draw) ∧
      (∀ v (p : G.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9) ∧
      IsEmpty (G.Coloring (Fin 3)) :=
  ⟨Steinberg.graph, Steinberg.planar_counterexample⟩

/-- info: 'challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms challenge
