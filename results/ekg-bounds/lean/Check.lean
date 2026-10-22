import Statement.TheoremTP3
import EKG3.AssemblyComputations
import FirstTerms

/-! Built by `lake build` (the default target). The build fails unless the
main theorem has exactly the stated type and every audited theorem depends
only on Lean's three standard axioms. -/

/-- The main theorem: Conjecture 3 of Lagarias, Rains and Sloane from the
four computed premises (`Statement/TheoremT.lean`, `Statement/TheoremTP3.lean`). -/
example : EKG3.FiniteFa → EKG3.FiniteFbP3 → EKG3.FiniteFcP3 →
    EKG3.CertifiedCoverP3 → EKG3.Conj3Statement :=
  EKG3.conj3_of_computations

/-- The conclusion, unfolded: for every `n = i+1 ≥ 1`, with `a(n) = actualA i`,
`13n ≤ 28a(n)` and `7a(n) ≤ 12n`, with equality only at `n = 28` and `n = 7`. -/
example : EKG3.Conj3Statement ↔ ∀ i : ℕ,
    (13*(i+1) ≤ 28*EKG.actualA i ∧ 7*EKG.actualA i ≤ 12*(i+1)) ∧
    (13*(i+1) = 28*EKG.actualA i ↔ i+1 = 28) ∧
    (7*EKG.actualA i = 12*(i+1) ↔ i+1 = 7) :=
  Iff.rfl

-- The sequence is the greedy sequence from 1 and 2 (`vendor/EKG/Canonical.lean`).
example : EKG.actualA = EKG.canonical.a := rfl
example : EKG.actualA 6 = 12 := EKG.FirstTerms.a7
example : EKG.actualA 27 = 13 := EKG.FirstTerms.a28

-- The analytic inputs, proved here rather than assumed.
example : EKG3.PiBoundsP3 := EKG3.piBoundsP3_holds
example : EKG3.ArithmeticLargeSieve := EKG3.arithmeticLargeSieve_holds

/-- info: 'EKG3.conj3_of_computations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.conj3_of_computations

/-- info: 'EKG3.P3.theoremT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.P3.theoremT

/-- info: 'EKG3.P3.lemmaF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.P3.lemmaF

/-- info: 'EKG3.piBoundsP3_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.piBoundsP3_holds

/-- info: 'EKG3.p3_psi_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.p3_psi_upper

/-- info: 'EKG3.p3_psi_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.p3_psi_lower

/-- info: 'EKG3.arithmeticLargeSieve_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.arithmeticLargeSieve_holds

/-- info: 'EKG3.largeSieveBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.largeSieveBT

/-- info: 'EKG3.G_gt_log_add_107' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.G_gt_log_add_107

/-- info: 'EKG3.lemmaA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.lemmaA

/-- info: 'EKG3.boundedCorollaryA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.boundedCorollaryA

/-- info: 'EKG3.lemmaC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.lemmaC

/-- info: 'EKG3.lemmaD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG3.lemmaD

/-- info: 'EKG.FirstTerms.a7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG.FirstTerms.a7

/-- info: 'EKG.FirstTerms.a28' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EKG.FirstTerms.a28
