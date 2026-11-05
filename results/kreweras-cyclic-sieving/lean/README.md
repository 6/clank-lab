# Lean details

A plain Lake project: Lean `leanprover/lean4:v4.34.0` (`lean-toolchain`) and Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435` (`lakefile.toml`, `lake-manifest.json`). From this folder:

```sh
lake exe cache get
lake build
```

The default targets are the library `RS16`, `Main.lean` (the statements) and `Axioms.lean`. There is no
`sorry`, `admit`, `axiom` declaration or `native_decide`. `Axioms.lean` checks with `#guard_msgs` that
each of the eleven theorems of `Main.lean` depends on exactly `propext`, `Classical.choice` and
`Quot.sound`, so the build fails if any other axiom appears. With Mathlib from the cache, the build took
about two minutes on two cores, with a peak of 7.4 GB of memory, almost all of it loading Mathlib.

## What is proved

Definitions are in `RS16/Defs.lean` and statements in `Main.lean` (namespace `RS16.Main`). The steps
are those of Section 2 of the paper.

| Theorem | Paper | Statement |
|---|---|---|
| `step2_fixed_points` | Step 2, Proposition 2.2 | `fixCount ℓ c cls (ν m₁) (h₁ m₁) X = Lval ℓ c cls h₁ ν e X m₁` |
| `step2_large_m2` | Lemma 2.3 | `ν > ℓ(c)` implies `Lval … = [X = [c]]` |
| `step3_rows` | Step 3, Proposition 2.4 | value `Σ_{j≤n} binom(m₁,j) a_j` at `m₁ = 1, …, n+1` implies the same at every `m₁ ≥ 1` |
| `rows_with_m1_factor` | Step 4, `d > b_max` | a row with factor `[m-1]_q` has value `0` |
| `conjecture_1_4` | Steps 1–4 | the theorem, from the checked facts |
| `checker_value` | checker A's last step | `F ≡ v (mod Φ_d)` implies value `v` at every primitive `d`-th root |
| `checker_exponents` | checker A's exponent loop | the loop keeps `h₁ ∣ ν e + j` |
| `exists_exponents` | | such exponents exist for every coprime `(h₁, ν)` |
| `reflection_length` | | `ℓ(w) = rank(w - 1)` satisfies the three length hypotheses |
| `value_of_polynomial`, `value_unique` | | what `HasValueAt` means |

The objects, as defined in `RS16/Defs.lean`:

- `HasValueAt f ω v`: `f = N/Q` with polynomials `N` and `Q`, `Q(ω) ≠ 0` and `v = N(ω)/Q(ω)`. For a
  polynomial this is evaluation (`value_of_polynomial`), and the value is unique (`value_unique`).
- `qint x = (1 - q^x)/(1 - q)`, and `Row`, the formulas of the shape both checkers accept. `Row.eval K
  row m` is the row as an element of `RatFunc K`. `numCount`, `dens` and `hasM1Factor` are checker A's
  `shape`, `const_brackets` and `has_m1_factor`.
- `IsDelta`, `rho`, `phi`, `fixCount`: delta sequences `(w₀; w₁, …, w_s)`, the twisted rotation, the
  Bessis–Reiner generator (6.4), and the number of delta sequences fixed by `φ^k` whose bottom `w₀`
  has class `X`.
- `ncC`, `chains`, `bottom`, `Uset`, `Lval`: `NC(W) ∩ C_G(c^{h₁})`, the chain counts `N_k(u)` by
  checker A's recursion, `w₀(u)`, the set `U_X`, and `L_X(m₁) = Σ_{k ≤ ℓ(c)} binom(m₁, k) Σ_{u ∈ U_X} N_k(u)`.

## The main statement

`RS16.Main.conjecture_1_4` is stated for any field `K` of characteristic 0, any finite group `G` with
a function `ℓ` that is subadditive (`hmul`), invariant under conjugation (`hconj`) and zero only at 1
(`hzero`), an element `c` with `c^h = 1` and `ℓ(c) > 0` (`n` is `ℓ(c)`), a class map `cls`, a row
`rows X` for each label and block exponents `e`. Its conclusion: for every `s ≥ 1`, every `k : ZMod (s * h)`
with `addOrderOf k = d`, every label `X` and every primitive `d`-th root `ω` in `K`,

```lean
HasValueAt ((rows X).eval K (s * h + 1)) ω (fixCount ℓ c cls s k.val X)
```

that is, row `X` at `m = sh + 1` is regular at `ω` and its value there is the number of delta
sequences fixed by `φ^k` whose bottom element has class `X`. An element of order `d` of `ℤ/shℤ` is a
`k` with `addOrderOf k = d`, acting by `φ^{k.val}`. Multichains `w₁ ≤ ⋯ ≤ w_s` are identified with
delta sequences by definition, the bottom `w₁` being `w₀`.

## Where each hypothesis is checked

Line numbers are those of `../checks/check_a.py`; checker B checks the same facts independently.

| Hypothesis | Instance | Checked by |
|---|---|---|
| `hmul`, `hconj`, `hzero` | `ℓ(w) = rank(w - 1)` (`ell`, line 86) | Lean, `reflection_length` |
| `hch`, `hn`, `ℓ(c) = n` | `c = s₁ ⋯ s_n` has order `h` and `rank(c - 1) = n` | `../checks/coxeter.py` |
| `he` | the exponents `ex[j+1]` of the loop at lines 540–548 | Lean, `checker_exponents`: each step keeps `h₁ ∣ ν e + j`, starting from `(0, 0)`; every block gets an exponent or the checker stops. Pairs the checker never uses get the exponents of `exists_exponents` |
| `hnum`, `hden` | `shape(a) ≤ n` and `len(const_brackets) ≤ n` | lines 495 and 506 |
| `hid` | `lhs == rhs(L, m₁ ν, d)` for `h₁ ∣ h`, `1 ≤ ν ≤ n`, `gcd(h₁, ν) = 1`, `m₁ = 1, …, n+2` | lines 523–575. `Lval` is lines 523–568; `rhs` is the exact polynomial (line 388) reduced modulo `Φ_d` (line 393), and `checker_value` turns that into `HasValueAt` |
| `hreg` | the row of the class of `c` is `q**(nm-n)` | line 511 |
| `hm1f` | every other row has a top-level `[m - 1]` factor | line 509 |
| `hbmax` | `b_max = maxden` | line 508 |
| `hlarge` | `rhs == [L = regular]` for `ν > n`, `ν (h/h₁) ≤ maxden`, `m₁ = 1, …, n+2` | lines 580–591 |

In the instance, `G` is `W` as integer matrices in root coordinates, `cls(w)` is the label of the class
of `V^w`, and `rows X` is row `X` of `../data/krew_tables.json` read in the grammar `Row`. Two facts
about checker A complete the match, and a reader confirms both from the code:

- Its rational-function arithmetic (`RF`, `ev`) computes `Row.eval` on rows of the accepted shape: its
  brackets are `1 + ⋯ + q^{x-1} = (1 - q^x)/(1 - q)` for `x ≥ 1`, and its exponents are `≥ 0`.
- Its `nc`, `down` and `rk` are `NC(W)`, the absolute order `ℓ(z) + ℓ(z⁻¹u) = ℓ(u)` and `ℓ`.

Outside Lean also remain the identification of reflection length with `rank(w - 1)` (Carter's lemma),
the formulas of Reiner and Sommers' Section 3.6 as they state them, and the labeling of orbits of
flats, which both checkers require to be a bijection with the table rows.

## Differences from the written proof

- Step 3 is proved by finite differences, as in the paper, so neither the positivity of the
  q-Kreweras numbers (Reiner and Sommers' Theorem 1.6(iv)) nor the check at `m₁ = n + 2` is used.
- Step 1's element of order `d` is a `k : ZMod (s * h)` with `addOrderOf k = d`, acting by `φ^{k.val}`.
