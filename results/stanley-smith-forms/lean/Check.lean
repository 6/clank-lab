import StanleySmithForms

-- Independent, fully qualified checks of the statements' exact types.

example : Matrix (Fin 6) (Fin 6) ℤ := StanleySmithForms.A
example : Matrix (Fin 6) (Fin 6) ℤ := StanleySmithForms.U
example : Matrix (Fin 6) (Fin 6) ℤ := StanleySmithForms.V

-- The matrix of `X₃` exactly as in the certificate (column `j` is the image of
-- basis vector `j`).
example : StanleySmithForms.A =
    !![ 2,  0,  0,  0,  0,  0;
       -1, -1,  0,  0,  0,  0;
        1,  0, -1,  0,  0,  0;
        0,  1,  0,  1,  0,  0;
        0,  0,  1,  0,  1,  0;
        0,  0,  0, -1, -1, -2] := rfl

example : StanleySmithForms.U.det = -1 := StanleySmithForms.U_det
example : StanleySmithForms.V.det = 1 := StanleySmithForms.V_det
example : StanleySmithForms.A.det = -4 := StanleySmithForms.A_det

example :
    StanleySmithForms.U * StanleySmithForms.A * StanleySmithForms.V =
      Matrix.diagonal ![1, 1, 1, 1, 2, 2] := StanleySmithForms.smith_form

example : (StanleySmithForms.A.map (Int.castRingHom (ZMod 2))).rank = 4 :=
  StanleySmithForms.rank_mod_two

example :
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * StanleySmithForms.A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4] :=
  StanleySmithForms.not_predicted

example :
    (IsUnit StanleySmithForms.U.det ∧ IsUnit StanleySmithForms.V.det ∧
      StanleySmithForms.U * StanleySmithForms.A * StanleySmithForms.V =
        Matrix.diagonal ![1, 1, 1, 1, 2, 2]) ∧
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * StanleySmithForms.A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4] :=
  StanleySmithForms.counterexample

example : StanleySmithForms.B =
    !![ 1,  0,  0,  0,  0,  0;
       -1, -2,  0,  0,  0,  0;
        1,  0, -2,  0,  0,  0;
        1,  2,  0,  2,  0,  0;
       -1,  0,  2,  0,  2,  0;
        0, -1, -1, -1, -1, -1] := rfl

example : StanleySmithForms.A * StanleySmithForms.B =
    2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := StanleySmithForms.A_mul_B
example : StanleySmithForms.B * StanleySmithForms.A =
    2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := StanleySmithForms.B_mul_A

-- The group ring identity with `X₃` and `(1 2)` written out, for every `n ≥ 3`
-- (points `1, 2, 3` are `0, 1, 2 : Fin n`).
example (n : ℕ) (hn : 3 ≤ n) :
    let X : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
      MonoidAlgebra.single (Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩) 1 +
        MonoidAlgebra.single (Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩) 1
    let T : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
      MonoidAlgebra.single (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) 1
    X * (X - T) = 2 ∧ (X - T) * X = 2 :=
  StanleySmithForms.group_ring_identity n hn

-- The same identity in `ℤ[S₅]`, the case of the witness.
example :
    let X : MonoidAlgebra ℤ (Equiv.Perm (Fin 5)) :=
      MonoidAlgebra.single (Equiv.swap 0 2) 1 + MonoidAlgebra.single (Equiv.swap 1 2) 1
    let T : MonoidAlgebra ℤ (Equiv.Perm (Fin 5)) := MonoidAlgebra.single (Equiv.swap 0 1) 1
    X * (X - T) = 2 ∧ (X - T) * X = 2 :=
  StanleySmithForms.group_ring_identity 5 (by norm_num)

-- The matrix step of the lattice argument, for any square integer matrices.
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B U V : Matrix ι ι ℤ} {d : ι → ℤ} (hAB : A * B = 2 • 1)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : U * A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = padicValInt 2 A.det :=
  StanleySmithForms.invariant_factors_of_mul_eq_two hAB hU hV hd

example {U V : Matrix (Fin 6) (Fin 6) ℤ} {d : Fin 6 → ℤ}
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hd : U * StanleySmithForms.A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = 2 :=
  StanleySmithForms.witness_factors hU hV hd

-- The counting step, with both lists written out.
example (f a b : ℕ) (hab : a + b ≤ f) :
    (∀ r, 1 ≤ r → r ≤ f →
      2 ^ ((if r ≤ a then 1 else 0) + (if r ≤ b then 1 else 0)) =
        (if r ≤ a + b then 2 else 1)) ↔ (a = 0 ∨ b = 0) :=
  StanleySmithForms.k3_counting f a b hab

-- Small values of the two lists.
example : StanleySmithForms.predFactor 1 1 1 = 4 := rfl
example : StanleySmithForms.actFactor 1 1 1 = 2 := rfl
example : StanleySmithForms.predFactor 2 0 2 = 2 := rfl
example : StanleySmithForms.actFactor 2 0 3 = 1 := rfl

-- The second witness, `λ = (5,2)`, `k = 7`.
example : Matrix (Fin 14) (Fin 14) ℤ := StanleySmithForms.A52
example : Matrix (Fin 14) (Fin 14) ℤ := StanleySmithForms.U52
example : Matrix (Fin 14) (Fin 14) ℤ := StanleySmithForms.V52

example : StanleySmithForms.A52 =
    !![ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       1,  1,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       1,  0,  0,  1,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       0,  1,  0,  1,  0,  4,  0,  0,  0,  0,  0,  0,  0,  0;
       0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
       1,  0,  0,  0,  0,  0,  1,  4,  0,  0,  0,  0,  0,  0;
       0,  1,  0,  0,  0,  0,  1,  0,  4,  0,  0,  0,  0,  0;
       0,  0,  0,  1,  0,  0,  1,  0,  0,  4,  0,  0,  0,  0;
       0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
     -3,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  4,  0,  0;
       1, -2,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  4,  0;
       1,  1,  0, -1,  0,  0,  0,  0,  0,  0,  1,  0,  0,  4] := rfl

example : IsUnit StanleySmithForms.U52.det := StanleySmithForms.U52_unimodular
example : IsUnit StanleySmithForms.V52.det := StanleySmithForms.V52_unimodular

example :
    StanleySmithForms.U52 * StanleySmithForms.A52 * StanleySmithForms.V52 =
      Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0] := StanleySmithForms.smith_form_52

example : StanleySmithForms.A52 * (StanleySmithForms.A52 - 4 • 1) = 0 :=
  StanleySmithForms.eigen_identity_52

example : StanleySmithForms.A52.charpoly = Polynomial.X ^ 5 * (Polynomial.X - 4) ^ 9 :=
  StanleySmithForms.charpoly_52

open Matrix in
example : ∀ μ : ℚ,
    (∃ v : Fin 14 → ℚ, v ≠ 0 ∧ (StanleySmithForms.A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔
      (μ = 0 ∨ μ = 4) := StanleySmithForms.eigenvalues_52

example : ∀ P Q : Matrix (Fin 14) (Fin 14) ℤ,
    IsUnit P.det → IsUnit Q.det → ∀ d, P * StanleySmithForms.A52 * Q = Matrix.diagonal d →
      ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i := StanleySmithForms.weak_remark_fails_52

open Matrix in
example :
    (IsUnit StanleySmithForms.U52.det ∧ IsUnit StanleySmithForms.V52.det ∧
      StanleySmithForms.U52 * StanleySmithForms.A52 * StanleySmithForms.V52 =
        Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0]) ∧
    (∀ μ : ℚ, (∃ v : Fin 14 → ℚ, v ≠ 0 ∧
        (StanleySmithForms.A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔ (μ = 0 ∨ μ = 4)) ∧
    (∀ P Q : Matrix (Fin 14) (Fin 14) ℤ, IsUnit P.det → IsUnit Q.det →
      ∀ d, P * StanleySmithForms.A52 * Q = Matrix.diagonal d → ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i) :=
  StanleySmithForms.counterexample_52

-- Both diagonal forms have the same determinant up to sign, so the determinant
-- alone does not distinguish them.
example : (Matrix.diagonal ![(1 : ℤ), 1, 1, 1, 2, 2]).det = 4 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]
example : (Matrix.diagonal ![(1 : ℤ), 1, 1, 1, 1, 4]).det = 4 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]

/-- info: 'StanleySmithForms.U_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.U_det

/-- info: 'StanleySmithForms.V_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.V_det

/-- info: 'StanleySmithForms.A_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.A_det

/-- info: 'StanleySmithForms.smith_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.smith_form

/-- info: 'StanleySmithForms.rank_mod_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.rank_mod_two

/-- info: 'StanleySmithForms.not_predicted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.not_predicted

/-- info: 'StanleySmithForms.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.counterexample

/-- info: 'StanleySmithForms.A_mul_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.A_mul_B

/-- info: 'StanleySmithForms.B_mul_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.B_mul_A

/--
info: 'StanleySmithForms.group_ring_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.group_ring_identity

/--
info: 'StanleySmithForms.invariant_factors_of_mul_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.invariant_factors_of_mul_eq_two

/--
info: 'StanleySmithForms.witness_factors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.witness_factors

/-- info: 'StanleySmithForms.k3_counting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms StanleySmithForms.k3_counting

/--
info: 'StanleySmithForms.U52_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.U52_unimodular

/--
info: 'StanleySmithForms.V52_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.V52_unimodular

/--
info: 'StanleySmithForms.smith_form_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.smith_form_52

/--
info: 'StanleySmithForms.eigen_identity_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.eigen_identity_52

/--
info: 'StanleySmithForms.charpoly_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.charpoly_52

/--
info: 'StanleySmithForms.eigenvalues_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.eigenvalues_52

/--
info: 'StanleySmithForms.weak_remark_fails_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.weak_remark_fails_52

/--
info: 'StanleySmithForms.counterexample_52' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StanleySmithForms.counterexample_52
