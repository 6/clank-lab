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
