import GR22.Main

/-! Theorem types, examples and kernel axiom guards. -/

example : GR22.FullEndpoint := GR22.fullEndpoint
example : GR22.ExpansionsExist := GR22.expansionsExist
example : GR22.Question1 := GR22.question1
example : GR22.Question1Positional := GR22.question1Positional
example : ¬ GR22.FullEndpointOffByOne := GR22.offByOne_false

open GR22 in
example : plethysm (complete 2) (complete 2) = schur [4] + schur [2, 2] :=
  anchor_h2_h2

open GR22 in
example : plethysm (complete 3) (complete 2) =
    schur [6] + schur [4, 2] + schur [2, 2, 2] := anchor_h3_h2

example (ns : List ℕ) (hns : ∀ n ∈ ns, 1 ≤ n) :
    ∃ c, GR22.SchurExpansion ns.prod (GR22.iterated ns) c :=
  GR22.iterated_has_expansion ns hns

#check @GR22.schurExpansion_unique

/-- info: 'GR22.fullEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.fullEndpoint

/-- info: 'GR22.expansionsExist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.expansionsExist

/-- info: 'GR22.schurExpansion_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.schurExpansion_unique

/-- info: 'GR22.question1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.question1

/-- info: 'GR22.iterated_has_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.iterated_has_expansion

/-- info: 'GR22.question1Positional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.question1Positional

/-- info: 'GR22.offByOne_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GR22.offByOne_false
