# Lean development

Run `lake exe cache get` and `lake build` in this directory. The default build checks the library `CK18HJ` and the file `Checks.lean`, which restates both theorems with their full types, guards their axioms and checks small examples of the definitions. The guarded axiom prints permit exactly `propext`, `Classical.choice` and `Quot.sound`. The proof does not use compiled evaluation; the examples are checked by the kernel with `decide`.

## Dependencies

- Lean **v4.32.2**, selected by `lean-toolchain`.
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c` (tag `v4.32.2`), selected by `lakefile.toml`.
- Transitive dependencies are pinned by revision in `lake-manifest.json`.

Mathlib and the Lean toolchain are obtained as dependencies; their source is not redistributed here.

## Statements and correspondence

The definitions and both statements are in `CK18HJ/Statement.lean` (55 lines):

```lean
def MainStatement : Prop :=
  ∀ Q K m n : ℕ, 1 ≤ Q → 32 * Q ≤ K * K → 2 * K + 2 ≤ m →
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, colour (32 * Q) (point w s) ≠ colour (32 * Q) (point w t)

def UnboundedStatement : Prop :=
  ∀ Q : ℕ, ∃ m : ℕ, ∀ n : ℕ, ∃ c : (Fin n → Fin m) → Bool,
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, c (point w s) ≠ c (point w t)
```

`CK18HJ.main : MainStatement` is the paper's Theorem 1, and `CK18HJ.unbounded : UnboundedStatement` is the existence statement behind Corollary 2 (its proof takes $m = 64(Q+1)+2$).

- Letters are `Fin m`, that is $0, \dots, m-1$, and positions are `Fin n`, numbered from 0 where the paper numbers them from 1.
- A root is `w : Fin n → Option (Fin m)`, with `none` for the wildcard; `∃ i, w i = none` says the wildcard set is nonempty. `point w t` replaces every wildcard by the letter `t`.
- `runs w` counts the wildcard positions that are first or follow a letter, which is the number of maximal intervals in the wildcard set.
- `S x` is the sum over positions of the squared difference between a letter and the one before it, as an integer, with the letter 0 before the first position. `colour B x` is `decide ((S x / B) % 2 = 1)`; since `S x` is nonnegative, integer division is the floor.
- The conclusion, two letters of the line with different colors, says the line is not monochromatic.

The quantity $I(m, r)$ is not defined in Lean; the step from these statements to the bound on it is the short argument of Corollary 2 in the paper.

## Layout

- `CK18HJ/Statement.lean`: the definitions and the two statements.
- `CK18HJ/Parabola.lean`: Lemmas 2 and 3 of the paper, in integer arithmetic; the lower side of the vertex is reduced to the upper side by $t \mapsto m - 1 - t$.
- `CK18HJ/Proof.lean`: Lemma 1, the run count, and the proofs of `main` and `unbounded`.
- `Checks.lean`: the restated statements, the axiom guards, and examples: the root with wildcards at positions 1, 3 and 4 over five letters has two runs, its point at 3 is the word 3 2 3 3, whose $S$ is 11, and an instance of the theorem for 14 letters.
