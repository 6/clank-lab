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

[Basic.lean](StanleySmithForms/Basic.lean) defines three $6 \times 6$ integer
matrices `A`, `U` and `V` as literals, copied unchanged from
[the witness certificate](../data/witness-311-k3.json). `A` is the matrix of
the Jucys–Murphy element $X_3 = (1\,3) + (2\,3)$ on the Specht module $S^{(3,1,1)}$,
in the standard polytabloid basis indexed by the standard Young tableaux

```
123/4/5, 124/3/5, 125/3/4, 134/2/5, 135/2/4, 145/2/3
```

in this order (rows separated by `/`), with column $j$ holding the
coordinates of $X_3$ applied to basis vector $j$:

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
$\operatorname{diag}(1,1,1,1,2,2)$ (the entries form a divisibility chain). The second
says that the form $\operatorname{diag}(1,1,1,1,1,4)$ predicted by Stanley's Conjecture
7.4 for $\lambda = (3,1,1)$, $k = 3$ cannot be reached from `A` by any unimodular row
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

Both diagonal forms have determinant $4$, so the determinant does not
separate them. The proof of `not_predicted` reduces modulo 2: reduction is
a ring homomorphism, so it keeps a unit determinant a unit; rank over
`ZMod 2` is unchanged by multiplication with invertible matrices (Mathlib's
`Matrix.rank_mul_eq_left_of_isUnit_det` and
`Matrix.rank_mul_eq_right_of_isUnit_det`); and the rank of a diagonal
matrix is its number of nonzero entries (`Matrix.rank_diagonal`). Through
`U` and `V`, `A` has rank $4$ over `ZMod 2`, while the predicted diagonal
matrix has five odd entries and so rank $5$.

## The group ring identity

[GroupRing.lean](StanleySmithForms/GroupRing.lean) proves an identity in the
integral group ring of the symmetric group, for every $n \geq 3$. Write
$s = (1\,3)$, $t = (2\,3)$ and $u = (1\,2)$, so that $X_3 = s + t$. Then
$X_3^2 = 2 + st + ts$, and $X_3 u = su + tu$ is the sum of the same two 3-cycles on
$\lbrace 1, 2, 3 \rbrace$, so $X_3(X_3 - u) = 2$, and likewise $(X_3 - u)X_3 = 2$. In Lean the
points $1, 2, 3$ are `0, 1, 2 : Fin n`, permutations multiply by composition,
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
for $n = 5$ with the literals `0, 1, 2`.

The step from this identity to modules is a written argument and is not
formalized: on any lattice stable under the permutations of $\lbrace 1, 2, 3 \rbrace$, the
matrix of $X_3$ times the matrix of $X_3 - (1\,2)$ is $2I$ in both orders, so every
invariant factor of $X_3$ on such a lattice divides $2$. For the witness, Lean
checks this concretely. `B` is the integer matrix $2A^{-1}$, and

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

The next section turns `A * B = 2 • 1` into a statement about the
invariant factors of `A`.

## Invariant factors and the counting step

[SmithFactors.lean](StanleySmithForms/SmithFactors.lean) formalizes the
matrix step of the lattice argument and the final counting step of the
$k = 3$ classification.

The matrix step holds for square integer matrices over any finite index
type:

```lean
theorem invariant_factors_of_mul_eq_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B U V : Matrix ι ι ℤ} {d : ι → ℤ} (hAB : A * B = 2 • 1)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : U * A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = padicValInt 2 A.det
```

Every diagonalization of `A` by unimodular matrices, the Smith normal form
in particular, has entries $\pm 1$ and $\pm 2$, and the number of even entries is the
2-adic valuation of $\det A$. The proof shows $D\,(V^{-1} B U^{-1}) = 2I$, so each
$d_i$ divides $2$, and compares 2-adic valuations of $\det U \cdot \det A \cdot \det V$ and
of the product of the $d_i$. Applied to the witness, with `A_mul_B` and
`A_det`:

```lean
theorem witness_factors {U V : Matrix (Fin 6) (Fin 6) ℤ} {d : Fin 6 → ℤ}
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : U * A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = 2
```

This is a second, lattice-style proof that the predicted entry $4$ cannot
occur, alongside `not_predicted`.

The counting step is pure arithmetic. Let $f$ be the number of standard
tableaux, and $a$ and $b$ the numbers of them with $3$ in the cells $(1,3)$ and
$(3,1)$, of contents $2$ and $-2$. Counting from the top, the conjecture predicts
the $r$-th invariant factor `predFactor a b r`. The actual one is
`actFactor a b r`: by the matrix step all factors are $1$ or $2$, and the number
of $2$s is the 2-adic valuation of $\det X_3$, which the content spectrum of $X_3$
(eigenvalues $1, -1, 2, -2$ with multiplicities given by the cells holding $3$)
makes $a + b$.

```lean
def predFactor (a b r : ℕ) : ℕ :=
  2 ^ ((if r ≤ a then 1 else 0) + (if r ≤ b then 1 else 0))

def actFactor (a b r : ℕ) : ℕ :=
  if r ≤ a + b then 2 else 1

theorem k3_counting (f a b : ℕ) (hab : a + b ≤ f) :
    (∀ r, 1 ≤ r → r ≤ f → predFactor a b r = actFactor a b r) ↔ (a = 0 ∨ b = 0)
```

So for $k = 3$ the two lists agree exactly when $3$ cannot reach one of the
cells $(1,3)$ and $(3,1)$; by the tableau facts below, that is when the shape
has fewer than three columns or fewer than three rows.

## The second witness: $\lambda = (5,2)$, $k = 7$

[Weak.lean](StanleySmithForms/Weak.lean) treats a second, larger witness.
`A52 : Matrix (Fin 14) (Fin 14) ℤ` is the matrix of
$X_7 = (1\,7) + (2\,7) + \cdots + (6\,7)$ on $S^{(5,2)}$, in the standard
polytabloid basis indexed by

```
12345/67, 12346/57, 12347/56, 12356/47, 12357/46, 12367/45, 12456/37,
12457/36, 12467/35, 12567/34, 13456/27, 13457/26, 13467/25, 13567/24
```

in this order, with column $j$ holding the coordinates of $X_7$ applied to
basis vector $j$. `A52`, `U52` and `V52` are copied unchanged from
[the certificate](../data/witness-52-k7.json); [Check.lean](Check.lean)
confirms `A52` against the literal entry by entry. The Smith normal form is
$\operatorname{diag}(1,1,1,1,2,4,4,4,4,0,0,0,0,0)$, while Stanley's
Conjecture 7.4 predicts $\operatorname{diag}(1,1,1,1,1,4,4,4,4,0,0,0,0,0)$.
This witness also refutes the weaker remark that every diagonal entry of the
Smith normal form is, up to sign, a product of eigenvalues: the only
eigenvalues are $0$ and $4$, and $2$ is no product of them. The main theorem
is

```lean
theorem counterexample_52 :
    (IsUnit U52.det ∧ IsUnit V52.det ∧
      U52 * A52 * V52 = Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0]) ∧
    (∀ μ : ℚ, (∃ v : Fin 14 → ℚ, v ≠ 0 ∧ (A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔
      (μ = 0 ∨ μ = 4)) ∧
    (∀ P Q : Matrix (Fin 14) (Fin 14) ℤ, IsUnit P.det → IsUnit Q.det →
      ∀ d, P * A52 * Q = Matrix.diagonal d → ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i)
```

with components

```lean
theorem U52_unimodular : IsUnit U52.det
theorem V52_unimodular : IsUnit V52.det
theorem smith_form_52 :
    U52 * A52 * V52 = Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0]
theorem eigen_identity_52 : A52 * (A52 - 4 • 1) = 0
theorem charpoly_52 : A52.charpoly = Polynomial.X ^ 5 * (Polynomial.X - 4) ^ 9
theorem eigenvalues_52 : ∀ μ : ℚ,
    (∃ v : Fin 14 → ℚ, v ≠ 0 ∧ (A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔
      (μ = 0 ∨ μ = 4)
theorem weak_remark_fails_52 : ∀ P Q : Matrix (Fin 14) (Fin 14) ℤ,
    IsUnit P.det → IsUnit Q.det → ∀ d, P * A52 * Q = Matrix.diagonal d →
      ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i
```

How they are proved:

- Unimodularity: explicit integer matrices `U52inv` and `V52inv` with
  `U52 * U52inv = 1` and `V52 * V52inv = 1`, then Mathlib's
  `Matrix.isUnit_det_of_right_inverse`. No $14 \times 14$ determinant is
  expanded.
- The matrix identities (the products above, $A_{52}^2 = 4A_{52}$ and the
  eigenvector equations) are checked with `decide +kernel`, which has the
  Lean kernel evaluate both sides entry by entry. It adds no axiom, unlike
  native code evaluation.
- The characteristic polynomial: `A52` is lower triangular, so its
  characteristic polynomial is the product of $x - a_{ii}$ over the diagonal,
  which has five entries $0$ and nine entries $4$.
- Eigenvalues: if $A_{52} v = \mu v$ with $v \neq 0$, then
  $A_{52}^2 = 4A_{52}$ gives $\mu^2 v = 4\mu v$, so $\mu(\mu - 4) = 0$.
  Conversely, explicit integer eigenvectors for $0$ and $4$ are exhibited.
- `weak_remark_fails_52` uses a parity certificate (the general lemma
  `exists_two_exact_of_certificate`): integer vectors $x, y, w, z$ with
  $A_{52}\,y = 2x$, $w^{\mathsf T} A_{52} = 2z^{\mathsf T}$ and
  $w \cdot x = 1$, read off from `U52` and `V52` at the diagonal entry $2$.
  For any unimodular $P$, $Q$ with $P A_{52} Q = D = \operatorname{diag}(d)$, set
  $x' = Px$, $y' = Q^{-1}y$ and $w' = (P^{-1})^{\mathsf T} w$. Then
  $d_i y'_i = 2x'_i$, $w'_i d_i$ is even for every $i$, and
  $w' \cdot x' = w \cdot x$ is odd. So some $i$ has $w'_i$ and $x'_i$ odd;
  then $d_i$ is even, and $d_i y'_i = 2x'_i$ with $x'_i$ odd rules out
  $4 \mid d_i$.

That an entry divisible by $2$ but not by $4$ is no product of eigenvalues is
immediate and not stated in Lean: a product of the eigenvalues $0$ and $4$ is
$1$ (the empty product), $0$ or a power of $4$, and each of these is odd or
divisible by $4$. Lean does not check that `A52` is the matrix of $X_7$ on
$S^{(5,2)}$, nor that the list above is Stanley's prediction; the certificate
checkers do.

## What the build checks

[Check.lean](Check.lean), part of the default build, restates every
statement above with fully qualified names and its exact type, checks that
`A` equals the certificate's matrix entry by entry and `B` its stated
literal, checks `A52` the same way, and audits each theorem
with `#guard_msgs in #print axioms`, so the build fails if any of them uses
an axiom beyond `propext`, `Classical.choice` and `Quot.sound` (`k3_counting`
uses only `propext` and `Quot.sound`, and its guard records exactly that). The
proofs use `simp`, `decide`, `decide +kernel`, `abel`, `omega` and Mathlib
lemmas, with no `sorry` and no native code evaluation.

## What Lean does not check

Lean checks the matrix computations for both witnesses, the group ring
identity, the matrix step of the lattice argument (from $AB = 2I$ to the
invariant factors) and the counting step. It does not check that the group
ring identity yields integer matrices $A$, $B$ with $AB = 2I$ on a lattice
stable under the permutations of $\lbrace 1, 2, 3 \rbrace$ (a written, elementary step);
the content spectrum of $X_3$ (classical, cited in the paper); or the tableau
facts that feed the counting step (only the cells $(1,2)$, $(2,1)$, $(1,3)$,
$(3,1)$ can hold $3$, with contents $1, -1, 2, -2$, and the partial fillings
extend to standard tableaux). It does not construct the Specht module from
its definition, so it does not check that `A` is the matrix of
$X_3$ on $S^{(3,1,1)}$ in the standard polytabloid basis, nor that
$(1,1,1,1,1,4)$ is the list Stanley's conjecture predicts for this case.
Likewise it does not check that `A52` is the matrix of $X_7$ on
$S^{(5,2)}$, nor the prediction for that case. For both witnesses, the
basis, the matrix and the prediction are checked by the two independent
certificate checkers, which recompute them from $\lambda$ and $k$; see
[their documentation](../checks/README.md).
