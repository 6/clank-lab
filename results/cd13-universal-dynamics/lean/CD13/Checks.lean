import CD13.Faithful

/-! Statement, boundary cases and axiom guards. -/

universe u

example : CD13.FullEndpoint.{u} := CD13.Faithful.full_endpoint

-- Empty graphs are included, with no nonempty-vertex hypothesis.
example : CD13.Acyclic (fun (_ _ : Empty) => False) := by
  intro i
  exact Empty.elim i

-- A one-coordinate update forgets its previous value and is idempotent.
private def oneSite : CD13.LocalSystem (fun (_ _ : Unit) => False) where
  S := fun _ => Bool
  finite := fun _ => inferInstance
  nonempty := fun _ => inferInstance
  localFn := fun _ _ => true

example : CD13.update oneSite () * CD13.update oneSite () = CD13.update oneSite () :=
  CD13.update_idempotent oneSite () (fun h => h)

-- The empty word acts as the identity, also on the empty product of states.
example {V : Type u} {E : V → V → Prop} (D : CD13.LocalSystem E) :
    CD13.eval D 1 = 1 := map_one _

/-- info: 'CD13.Faithful.full_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CD13.Faithful.full_endpoint

/-- info: 'CD13.Faithful.constructor_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CD13.Faithful.constructor_separates

/-- info: 'CD13.Recovery.projection_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CD13.Recovery.projection_endpoint
