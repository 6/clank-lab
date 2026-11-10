import Pentagon

/-! Statement, axiom and example checks for the public build. -/

/-- The main theorem, restated with its full type. -/
example (small : Pentagon.AsymPeriod 8 ∧ Pentagon.AsymPeriod 10 ∧ Pentagon.AsymPeriod 30 ∧
      Pentagon.AsymPeriod 42 ∧ Pentagon.AsymPeriod 58 ∧ Pentagon.AsymPeriod 102) :
    ∀ n : Nat, 0 < n → n % 2 = 0 → n ≠ 2 → n ≠ 12 → n ≠ 14 → n ≠ 18 → Pentagon.AsymPeriod n :=
  Pentagon.dl_conjecture_4_3_existence small

/-- The arithmetic theorem behind it, with no cited input. -/
example (l : Nat) (h2 : 2 ≤ l) (hl : l ∉ [4, 5, 6, 7, 9, 15, 21, 29, 51]) :
    ∃ v, Pentagon.Orbit v ∧ Pentagon.ell v = l ∧ Pentagon.Asym v :=
  Pentagon.long_half_periods l h2 hl

/-- The cited input, Kontorovich–Zhang Theorem 2.1, as the axiom states it. -/
example : ∀ v : Pentagon.Vec, Pentagon.Orbit v → Pentagon.Asym v →
    Pentagon.AsymPeriod (2 * Pentagon.ell v) :=
  Pentagon.kz_thm_2_1

/-- info: 'Pentagon.dl_conjecture_4_3_existence' depends on axioms: [propext, Classical.choice, Pentagon.kz_thm_2_1, Quot.sound] -/
#guard_msgs in
#print axioms Pentagon.dl_conjecture_4_3_existence

/-- info: 'Pentagon.long_half_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pentagon.long_half_periods

/-- info: 'Pentagon.exceptions_combinatorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pentagon.exceptions_combinatorial

namespace Pentagon.PublicChecks
open Pentagon

/-! Examples. The generator A acts as the matrix [[1, φ], [0, 1]]: A · (0, 1) = (φ, 1). -/
example : A.act ⟨ZPhi.zero, ZPhi.one⟩ = ⟨ZPhi.phi, ZPhi.one⟩ := by decide

/-- (φ, 2 + φ) = B · A · (0, 1) is in the orbit, with ℓ = 4, and it is symmetric:
(1 − 1) + 2(2 − 0) = 4 is not divisible by 5. -/
example : Orbit ⟨⟨0, 1⟩, ⟨2, 1⟩⟩ ∧ ell ⟨⟨0, 1⟩, ⟨2, 1⟩⟩ = 4 ∧ ¬ Asym ⟨⟨0, 1⟩, ⟨2, 1⟩⟩ := by
  refine ⟨?_, by decide, by unfold Asym; decide⟩
  have h1 : Orbit (A.act ⟨ZPhi.zero, ZPhi.one⟩) := Orbit.step (by simp) Orbit.base
  exact Orbit.step (M := B) (by simp) h1

/-- A half-period from the covering: some asymmetric orbit vector has ℓ = 1000. -/
example : ∃ v, Orbit v ∧ ell v = 1000 ∧ Asym v := long_half_periods 1000 (by decide) (by decide)

end Pentagon.PublicChecks
