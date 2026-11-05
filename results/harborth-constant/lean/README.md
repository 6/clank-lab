# Lean development

Run `lake exe cache get` and `lake build` in this directory. The default build checks the library `Harborth`, the file `Main.lean` with the three main theorems, and the file `Checks.lean`, which restates the theorems with the definition unfolded, guards their axioms and checks small examples of the definition. The guarded axiom prints permit exactly `propext`, `Classical.choice` and `Quot.sound`. The finite checks for $p = 11$ and $13$ run by `decide +kernel`, which evaluates in Lean's kernel and adds no axiom; the proof does not use compiled evaluation.

## Dependencies

- Lean **v4.34.0**, selected by `lean-toolchain`.
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, selected by `lakefile.toml`.
- Transitive dependencies are pinned by revision in `lake-manifest.json`.

Mathlib and the Lean toolchain are obtained as dependencies; their source is not redistributed here.

A clean build after `lake exe cache get` takes about three minutes on one core and peaks at about 9 GB of memory, in `Harborth/ShapeSmall.lean`.

## Statements and correspondence

The definition is in `Harborth/Lift.lean` and the theorems in `Main.lean`:

```lean
def HasZeroSumPSubset (p : ℕ) (S : Finset (ZMod p × ZMod p)) : Prop :=
  ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0

theorem upper (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (S : Finset (ZMod p × ZMod p)) (hS : S.card = 2 * p - 1) :
    HasZeroSumPSubset p S

theorem lower (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ∃ S : Finset (ZMod p × ZMod p), S.card = 2 * p - 2 ∧ ¬ HasZeroSumPSubset p S

theorem harborth_constant (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    sInf {k : ℕ | ∀ S : Finset (ZMod p × ZMod p), S.card = k → HasZeroSumPSubset p S}
      = 2 * p - 1
```

- `ZMod p × ZMod p` is the group $C_p\oplus C_p$, and a `Finset` has distinct elements, so `HasZeroSumPSubset p S` says that $S$ contains $p$ distinct elements whose sum is zero; $p$ is the exponent of the group.
- `upper` is the theorem of the paper, for every prime $p\ge 11$; `lower` is the lower bound, for every odd prime.
- The set in `harborth_constant` contains $2p-1$ by `upper` and no smaller $k$ by `lower` (a smaller set inside the lower-bound example has no such subset either), so its infimum is the Harborth constant. The natural-number subtractions are of smaller numbers.
- Kemnitz's cases $p = 3, 5, 7$ are not part of the formal proof.

## Layout

- `Harborth/DSH.lean`, `Harborth/DSHAux.lean`: the theorem of Dias da Silva and Hamidoune in `ZMod p`, by the polynomial method of Alon, Nathanson and Ruzsa from Mathlib's Combinatorial Nullstellensatz.
- `Harborth/LiftCore.lean`, `Harborth/LiftAvg.lean`, `Harborth/Lift.lean`: directions and projections, the lifting criterion (with Mathlib's Cauchy–Davenport theorem), full lines, the averaging over the $p+1$ directions, and the reduction of the theorem to the profile proposition (Section 2 of the paper).
- `Harborth/SLC.lean`, `Harborth/SLCAux.lean`: the symmetric layer criterion and the exceptional shapes (Sections 3 and 5).
- `Harborth/ShapeDefs.lean`, `Harborth/ShapeLarge.lean`, `Harborth/Shape.lean`: rules B and H and the Shape Lemma for $p\ge 17$ (Section 4); Case 3 is proved with integer inequalities in place of the square roots of Appendix A.
- `Harborth/ShapeSmall.lean`: the finite check for $p = 11$ and $13$ (Section 6). It enumerates every sorted profile, proves that the enumeration is complete, and checks each concentrated one by kernel evaluation, with the three depth lists of Table 1 at $p = 11$.
- `Harborth/CPL.lean`: the profile proposition, from the pieces above.
- `Main.lean`: the three theorems. `Checks.lean`: the restatements, axiom guards and examples.
