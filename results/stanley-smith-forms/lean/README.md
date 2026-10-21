# Lean proof

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib dependency are pinned in `lean-toolchain`,
`lakefile.toml` and the standard Lake dependency manifest: Lean 4.34.0 and
the Mathlib commit named in `lakefile.toml`. Only dependency artifacts come
from the Mathlib cache; Lake checks the local proof sources. After the cache
download, the build takes under a minute.

## What is stated

[Basic.lean](StanleySmithForms/Basic.lean) defines three 6 × 6 integer
matrices `A`, `U` and `V` as literals, copied unchanged from
[the witness certificate](../data/witness-311-k3.json). `A` is the matrix of
the Jucys–Murphy element X₃ = (1 3) + (2 3) on the Specht module S^(3,1,1),
in the standard polytabloid basis indexed by the standard Young tableaux

```
123/4/5, 124/3/5, 125/3/4, 134/2/5, 135/2/4, 145/2/3
```

in this order (rows separated by `/`), with column j holding the
coordinates of X₃ applied to basis vector j:

```lean
def A : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0,  0,  0,  0,  0;
     -1, -1,  0,  0,  0,  0;
      1,  0, -1,  0,  0,  0;
      0,  1,  0,  1,  0,  0;
      0,  0,  1,  0,  1,  0;
      0,  0,  0, -1, -1, -2]
```

The main theorem, `StanleySmithForms.counterexample`, is

```lean
theorem counterexample :
    (IsUnit U.det ∧ IsUnit V.det ∧ U * A * V = Matrix.diagonal ![1, 1, 1, 1, 2, 2]) ∧
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4]
```

The first part says that the Smith normal form of `A` is
diag(1, 1, 1, 1, 2, 2) (the entries form a divisibility chain). The second
says that the form diag(1, 1, 1, 1, 1, 4) predicted by Stanley's Conjecture
7.4 for λ = (3,1,1), k = 3 cannot be reached from `A` by any unimodular row
and column operations. Since the Smith normal form is unique, this is the
disagreement with the conjecture.

The same file proves the component statements, all in the namespace
`StanleySmithForms`:

```lean
theorem U_det : U.det = -1
theorem V_det : V.det = 1
theorem A_det : A.det = -4
theorem smith_form : U * A * V = Matrix.diagonal ![1, 1, 1, 1, 2, 2]
theorem rank_mod_two : (A.map (Int.castRingHom (ZMod 2))).rank = 4
theorem not_predicted :
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4]
```

Both diagonal forms have determinant 4, so the determinant does not
separate them. The proof of `not_predicted` reduces modulo 2: reduction is
a ring homomorphism, so it keeps a unit determinant a unit; rank over
`ZMod 2` is unchanged by multiplication with invertible matrices (Mathlib's
`Matrix.rank_mul_eq_left_of_isUnit_det` and
`Matrix.rank_mul_eq_right_of_isUnit_det`); and the rank of a diagonal
matrix is its number of nonzero entries (`Matrix.rank_diagonal`). Through
`U` and `V`, `A` has rank 4 over `ZMod 2`, while the predicted diagonal
matrix has five odd entries and so rank 5.

## The group ring identity

[GroupRing.lean](StanleySmithForms/GroupRing.lean) proves an identity in the
integral group ring of the symmetric group, for every n ≥ 3. Write
s = (1 3), t = (2 3) and u = (1 2), so that X₃ = s + t. Then
X₃² = 2 + st + ts, and X₃u = su + tu is the sum of the same two 3-cycles on
{1, 2, 3}, so X₃(X₃ − u) = 2, and likewise (X₃ − u)X₃ = 2. In Lean the
points 1, 2, 3 are `0, 1, 2 : Fin n`, permutations multiply by composition,
and

```lean
noncomputable def X3 (n : ℕ) (hn : 3 ≤ n) : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  single (Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩) 1 +
    single (Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩) 1

noncomputable def T12 (n : ℕ) (hn : 3 ≤ n) : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  single (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) 1

theorem group_ring_identity (n : ℕ) (hn : 3 ≤ n) :
    X3 n hn * (X3 n hn - T12 n hn) = 2 ∧ (X3 n hn - T12 n hn) * X3 n hn = 2
```

[Check.lean](Check.lean) restates it with `X3` and `T12` written out, and
for n = 5 with the literals `0, 1, 2`.

The step from this identity to modules is a written argument and is not
formalized: on any lattice stable under the permutations of {1, 2, 3}, the
matrix of X₃ times the matrix of X₃ − (1 2) is 2I in both orders, so every
invariant factor of X₃ on such a lattice divides 2. For the witness, Lean
checks this concretely. `B` is the integer matrix 2A⁻¹, and

```lean
theorem A_mul_B : A * B = 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ)
theorem B_mul_A : B * A = 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ)
```

with

```lean
def B : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 1,  0,  0,  0,  0,  0;
     -1, -2,  0,  0,  0,  0;
      1,  0, -2,  0,  0,  0;
      1,  2,  0,  2,  0,  0;
     -1,  0,  2,  0,  2,  0;
      0, -1, -1, -1, -1, -1]
```

By the standard argument (if P A Q = D with P, Q unimodular and D
diagonal, then D (Q⁻¹ B P⁻¹) = 2I), this rules out an invariant factor 4 as
the conjecture predicts; that deduction is not formalized here, and
`not_predicted` above is the formal statement that the predicted form is
unreachable.

## What the build checks

[Check.lean](Check.lean), part of the default build, restates every
statement above with fully qualified names and its exact type, checks that
`A` equals the certificate's matrix entry by entry and `B` its stated
literal, and audits each theorem
with `#guard_msgs in #print axioms`, so the build fails if any of them uses
an axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The proofs
use `simp`, `decide`, `abel` and Mathlib lemmas, with no `sorry` and no native
code evaluation.

## What Lean does not check

Lean checks the matrix computation and the group ring identity only. It
does not construct the Specht module from its definition, so it does not
check that `A` is the matrix of
X₃ on S^(3,1,1) in the standard polytabloid basis, nor that
(1, 1, 1, 1, 1, 4) is the list Stanley's conjecture predicts for this case.
Both are checked by the two independent certificate checkers, which
recompute the basis, the matrix and the prediction from λ and k; see
[their documentation](../checks/README.md). The written arguments in the
paper (the passage from the group ring identity to lattices, other lattices,
other shapes) are not formalized.
