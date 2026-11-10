# Lean development

Run `lake build` in this directory. The project uses core Lean only, with no external libraries; `lean-toolchain` selects Lean v4.34.0 and `lake-manifest.json` lists no dependencies. The default build checks the library `Pentagon` and the file `PublicChecks.lean`, which restates the main theorems with their full types, guards their axioms and checks a few examples. The finite verifications are evaluated by the kernel (`decide +kernel`); the proof does not use compiled evaluation.

## Statements and correspondence

The definitions are in `Pentagon/Statement.lean`.

- `ZPhi` is a pair of natural numbers `p`, `q`, read as $p + q\varphi$ with $\varphi^2 = \varphi + 1$; its product is $(p + q\varphi)(r + s\varphi) = pr + qs + (ps + qr + qs)\varphi$. Natural numbers suffice because every entry of the four generators, and so every vector of the orbit, has nonnegative coefficients.
- `Vec` is a column vector $(x, y)$ of two such numbers, and `Mat` a 2 × 2 matrix acting on it by `Mat.act`.
- `A`, `B`, `C`, `D` are the generators of Kontorovich and Zhang's semigroup $\Gamma^+$, with rows (1, φ), (0, 1); (1, 0), (φ, 1); (φ, φ), (1, φ); and (φ, 1), (φ, φ), written entrywise.
- `Orbit v` is the inductive predicate for $v \in \Gamma^+ \cdot (0,1)^t$: it holds for $(0, 1)$ and is preserved by each generator.
- For $v = (a + b\varphi, c + d\varphi)$, `ell v` is $a + b + c + d$ and `Asym v` says that $(d-b) + 2(c-a)$, computed in the integers, is divisible by 5.
- `AsymPeriod n` is an opaque proposition, read as "some asymmetric periodic billiard trajectory in the regular pentagon has combinatorial period $n$". Billiards are not formalized. It enters only through the axiom below and the hypothesis of the main theorem.

The cited input is the axiom

```lean
axiom kz_thm_2_1 : ∀ v : Vec, Orbit v → Asym v → AsymPeriod (2 * ell v)
```

Its documentation quotes Kontorovich and Zhang's Theorem 2.1 and the sentence before it, which identifies the long saddle connections in the first quadrant with the orbit, so that the theorem applies to every `Orbit` vector. Only the theorem's first case, period $2\ell$ for asymmetric trajectories, is assumed.

The main theorem, in `Pentagon/Proof.lean`, is

```lean
theorem dl_conjecture_4_3_existence
    (small : AsymPeriod 8 ∧ AsymPeriod 10 ∧ AsymPeriod 30 ∧ AsymPeriod 42 ∧ AsymPeriod 58 ∧
      AsymPeriod 102) :
    ∀ n : Nat, 0 < n → n % 2 = 0 → n ≠ 2 → n ≠ 12 → n ≠ 14 → n ≠ 18 → AsymPeriod n
```

The hypothesis `small` is the paper's Proposition 5.1, checked outside Lean by the programs in `../checks/`. The paper's Proposition 4.1 is

```lean
theorem long_half_periods (l : Nat) (h2 : 2 ≤ l) (hl : l ∉ exceptions) :
    ∃ v, Orbit v ∧ ell v = l ∧ Asym v
```

with `exceptions` the list 4, 5, 6, 7, 9, 15, 21, 29, 51.

## Axioms

`PublicChecks.lean` guards the axiom lists with `#guard_msgs`. `Pentagon.long_half_periods` depends on `propext`, `Classical.choice` and `Quot.sound` only; `Pentagon.dl_conjecture_4_3_existence` depends on these and `Pentagon.kz_thm_2_1`. `Pentagon.exceptions_combinatorial`, which says that no asymmetric orbit vector $v$ has $\ell(v)$ or $\ell(\varphi v)$ in {1, 6, 7, 9}, depends on the three standard axioms only; the main theorem does not use it.

## Layout

- `Pentagon/Statement.lean`: the definitions and the axiom.
- `Pentagon/Cert.lean`: the 379 families, grouped by the depth of the tree nodes they close, each as $(m, s, w, P, u, n_0)$ with words written as lists of generator indices (0 to 3 for `A` to `D`, and 0 or 1 for the parabolic `A` or `B`); the prime order 5, 5, 2, 3, 2, 7, 2, 3, 2, 11, 13, 43 of the splitting; and the list of orbit vectors with $\ell \le 9$ used by `exceptions_combinatorial`.
- `Pentagon/Proof.lean`: the coordinate form of the generators (`act_A` to `act_D`), the parabolic powers $P^n = I + nN$ (`powP_succ`), the families (`famOK`, `fam_sound`; the paper's Lemma 3.1), the tree and its closing condition (`chk`, `leafOK`, `leaf_sound`, `chk_sound`; Lemma 4.2), the kernel checks `chk_order` and `levels_ok`, and the theorems above.
- `PublicChecks.lean`: the statement and axiom checks, and three examples: the action of `A`, the symmetric orbit vector $(\varphi, 2 + \varphi) = BA \cdot (0,1)^t$ with $\ell = 4$, and an asymmetric orbit vector with $\ell = 1000$ obtained from the covering.

## What is outside Lean

The period theorem of Davis, Fuchs and Tabachnikov, in Kontorovich and Zhang's form, is the axiom above and is not formalized; neither are billiards, the golden L surface or its saddle connections. The six explicit trajectories are checked by the programs in `../checks/`.
